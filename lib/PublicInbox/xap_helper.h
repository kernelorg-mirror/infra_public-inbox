/*
 * Copyright (C) all contributors <meta@public-inbox.org>
 * License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>
 *
 * Standalone helper process using C and minimal C++ for Xapian,
 * this is not linked to Perl in any way.
 * C (not C++) is used as much as possible to lower the contribution
 * barrier for hackers who mainly know C (this includes the maintainer).
 * Yes, that means we use C stdlib stuff like open_memstream
 * instead of their equivalents in the C++ stdlib :P
 * Everything here is an unstable internal API of public-inbox and
 * NOT intended for ordinary users; only public-inbox hackers
 *
 * As of public-inbox 2.2+, lei forks a subprocess on every request
 * to scale to local demand.  Public-facing use is prefork-only,
 * since we expect public-facing servers to have dedicated resources
 * allocated for it and local user software to have more dynamic
 * resource usage.
 */
#ifndef _ALL_SOURCE
#	define _ALL_SOURCE
#endif
#ifndef _GNU_SOURCE
#	define _GNU_SOURCE
#endif
#if defined(__NetBSD__) && !defined(_OPENBSD_SOURCE) // for reallocarray(3)
#	define _OPENBSD_SOURCE
#endif
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <poll.h>

#include <assert.h>
#include <err.h> // BSD, glibc, and musl all have this
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sysexits.h>
#include <unistd.h>
#include <xapian.h> // our only reason for using C++

#define MY_VER(maj,min,rev) ((maj) << 16 | (min) << 8 | (rev))
#define XAP_VER \
	MY_VER(XAPIAN_MAJOR_VERSION,XAPIAN_MINOR_VERSION,XAPIAN_REVISION)

#if XAP_VER >= MY_VER(1,3,6)
#	define NRP Xapian::NumberRangeProcessor
#	define RP Xapian::RangeProcessor
#	define ADD_RP add_rangeprocessor
#	define SET_MAX_EXPANSION set_max_expansion // technically 1.3.3
#else
#	define NRP Xapian::NumberValueRangeProcessor
#	define ADD_RP add_valuerangeprocessor
#	define SET_MAX_EXPANSION set_max_wildcard_expansion
#endif

#if defined(__GLIBC__)
#	define MY_DO_OPTRESET() do { optind = 0; } while (0)
#else /* FreeBSD, musl, dfly, NetBSD, OpenBSD */
#	define MY_DO_OPTRESET() do { optind = optreset = 1; } while (0)
#endif

#if defined(__DragonFly__) || defined(__FreeBSD__) || defined(__GLIBC__)
#	define STDERR_ASSIGNABLE (1)
#else
#	define STDERR_ASSIGNABLE (0)
#endif

// assert functions are used correctly (e.g. ensure hackers don't
// cause EINVAL/EFAULT).  Not for stuff that can fail due to HW
// failures.
# define CHECK(type, expect, expr) do { \
	type ckvar______ = (expr); \
	assert(ckvar______ == (expect) && "BUG" && __FILE__ && __LINE__); \
} while (0)

// coredump on most usage errors since our only users are internal
#define ABORT(...) do { warnx(__VA_ARGS__); abort(); } while (0)
#define EABORT(...) do { warn(__VA_ARGS__); abort(); } while (0)

static void *xcalloc(size_t nmemb, size_t size)
{
	void *ret = calloc(nmemb, size);
	if (!ret) EABORT("calloc(%zu, %zu)", nmemb, size);
	return ret;
}

#if defined(__GLIBC__) && defined(__GLIBC_MINOR__) && \
		MY_VER(__GLIBC__, __GLIBC_MINOR__, 0) >= MY_VER(2, 28, 0)
#	define HAVE_REALLOCARRAY 1
#elif defined(__OpenBSD__) || defined(__DragonFly__) || \
		defined(__FreeBSD__) || defined(__NetBSD__)
#	define HAVE_REALLOCARRAY 1
#endif

static void *xreallocarray(void *ptr, size_t nmemb, size_t size)
{
#ifdef HAVE_REALLOCARRAY
	void *ret = reallocarray(ptr, nmemb, size);
#else // everyone has g++ >=5 these days, right?
	void *ret = NULL;

	if (__builtin_mul_overflow(nmemb, size, 0))
		errno = ENOMEM;
	else
		ret = realloc(ptr, nmemb * size);
#endif
	if (!ret) EABORT("reallocarray(..., %zu, %zu)", nmemb, size);
	return ret;
}

#include "khashl.h"

struct srch {
	int ckey_len; // int for comparisons
	unsigned qp_flags;
	Xapian::Database *db;
	Xapian::QueryParser *qp;
	unsigned char ckey[]; // $shard_path0\0$shard_path1\0...
};

static khint_t srch_hash(const struct srch *srch)
{
	return kh_hash_bytes(srch->ckey_len, srch->ckey);
}

static int srch_eq(const struct srch *a, const struct srch *b)
{
	return a->ckey_len == b->ckey_len ?
		!memcmp(a->ckey, b->ckey, (size_t)a->ckey_len) : 0;
}

KHASHL_CSET_INIT(KH_LOCAL, srch_set, srch_set, struct srch *,
		srch_hash, srch_eq)
static srch_set *srch_cache;
static struct req *cur_req; // for ThreadFieldProcessor
static long my_fd_max, shard_nfd;
// sock_fd is modified in signal handler, yes, it's SOCK_SEQPACKET
static volatile int sock_fd = STDIN_FILENO;
static sigset_t fullset, workerset;
static bool alive = true;
static bool lei; // support kw: and L: prefixes, FLAG_PHRASE always
#if STDERR_ASSIGNABLE
static FILE *orig_err = stderr;
#endif
static int orig_err_fd = -1;
static pid_t *worker_pids; // nr => pid
#define WORKER_MAX USHRT_MAX
static unsigned long nworker, nworker_hwm;
static int pipefds[2];
static const char *stdout_path, *stderr_path; // for SIGUSR1
static sig_atomic_t worker_needs_reopen;
static Xapian::FieldProcessor *thread_fp;

// PublicInbox::Search and PublicInbox::CodeSearch generate these:
static void mail_rp_init(void);
static void code_nrp_init(void);
static void qp_init_mail_search(Xapian::QueryParser *);
static void qp_init_code_search(Xapian::QueryParser *);

enum exc_iter {
	ITER_OK = 0,
	ITER_RETRY,
	ITER_ABORT
};

#define MY_ARG_MAX 256 // FIXME too small?
typedef bool (*cmd)(struct req *);

enum input_state {
	IN_RBUF = 0, // the default
	IN_FILE_MAYBE,
	IN_FILE // sender used prepare_buf_as_io
};

// only one request per-process since we have RLIMIT_CPU timeout
struct req { // argv and pfxv point into global rbuf
	char *lockv[MY_ARG_MAX]; // open.lock files
	char *argv[MY_ARG_MAX];
	char *pfxv[MY_ARG_MAX]; // -A <prefix>
	char *qpfxv[MY_ARG_MAX]; // -Q <user_prefix>[:=]<INTERNAL_PREFIX>
	char *dirv[MY_ARG_MAX]; // -d /path/to/XDB(shard)
	size_t *lenv; // -A <prefix>LENGTH
	struct srch *srch;
	char *Pgit_dir;
	char *Oeidx_key;
	cmd fn;
	unsigned long long max;
	unsigned long long off;
	unsigned long long threadid;
	unsigned long long uid_min, uid_max;
	unsigned long timeout_sec;
	size_t nr_out;
	long sort_col; // value column, negative means BoolWeight
	int argc, pfxc, qpfxc, dirc, lockc;
	FILE *fp[3];
		// [ [ input file (optional if input_state=IN_FILE) ],
		// [ response pipe|sock, status/errors (optional) ]
	bool collapse_threads;
	bool code_search;
	bool relevance; // sort by relevance before column
	bool asc; // ascending sort
};

struct fbuf {
	FILE *fp;
	char *ptr;
	size_t len;
};

struct open_locks {
	struct req *req;
	int lock_fd[]; // counted by req->lockc
};

#define SPLIT2ARGV(dst,buf,len) split2argv(dst,buf,len,MY_ARRAY_SIZE(dst))
static size_t split2argv(char **dst, char *buf, size_t len, size_t limit)
{
	if (buf[0] == 0 || len == 0 || buf[len - 1] != 0)
		ABORT("bogus argument given");
	size_t nr = 0;
	char *c = buf;
	for (size_t i = 1; i < len; i++) {
		if (!buf[i]) {
			dst[nr++] = c;
			c = buf + i + 1;
		}
		if (nr == limit)
			ABORT("too many args: %zu == %zu", nr, limit);
	}
	if (nr == 0) ABORT("no argument given");
	if ((long)nr < 0) ABORT("too many args: %zu", nr);
	return (long)nr;
}

static bool has_threadid(const struct srch *srch)
{
	return srch->db->get_metadata("has_threadid") == "1";
}

static Xapian::Enquire prep_enquire(const struct req *req)
{
	Xapian::Enquire enq(*req->srch->db);
	if (req->sort_col < 0) {
		enq.set_weighting_scheme(Xapian::BoolWeight());
		enq.set_docid_order(req->asc ? Xapian::Enquire::ASCENDING
					: Xapian::Enquire::DESCENDING);
	} else if (req->relevance) {
		enq.set_sort_by_relevance_then_value(req->sort_col, !req->asc);
	} else {
		enq.set_sort_by_value_then_relevance(req->sort_col, !req->asc);
	}
	return enq;
}

static void xclose(int fd)
{
	if (close(fd) < 0 && errno != EINTR)
		EABORT("BUG: close");
}

// __attribute__((__unused__)) keeps clang happy (tested 14.0.5 on FreeBSD)
#define AUTO_UNLOCK __attribute__((__cleanup__(unlock_ensure))) \
		__attribute__((__unused__))
static void unlock_ensure(void *ptr)
{
	struct open_locks **lk_ = (struct open_locks **)ptr;
	struct open_locks *lk = *lk_;

	if (!lk)
		return;
	for (int i = 0; i < lk->req->lockc; i++)
		if (lk->lock_fd[i] >= 0)
			xclose(lk->lock_fd[i]); // implicit LOCK_UN
	free(lk);
}

static struct open_locks *lock_shared_maybe(struct req *req)
{
	struct open_locks *lk = NULL;
	size_t size;

	assert(req->dirc);
	if (!req->lockc) {
		warn("W: %s has no -l (open.lock)", req->dirv[0]);
		return NULL;
	}
	assert(req->lockc > 0);
	assert(req->lockc < MY_ARG_MAX);
	if (__builtin_mul_overflow(sizeof(int), (size_t)req->lockc, &size)) {
		warnx("W: too many locks (%d)", req->lockc);
		return NULL;
	}
	if (__builtin_add_overflow(sizeof(*lk), size, &size)) {
		warnx("W: too many locks (%d)", req->lockc);
		return NULL;
	}
	lk = (struct open_locks *)malloc(size);
	if (!lk) EABORT("malloc(%zu)", size);
	lk->req = req;
	for (int i = 0; i < req->lockc; i++) {
		lk->lock_fd[i] = open(req->lockv[i], O_RDONLY);

		if (lk->lock_fd[i] < 0) {
			if (errno != ENOENT)
				warn("W: open(%s)", req->lockv[i]);
			continue;
		}
		while (flock(lk->lock_fd[i], LOCK_SH) < 0) {
			if (errno == EINTR)
				continue;
			warn("W: flock(%s, LOCK_SH)", req->lockv[i]);
			break;
		}
	}
	return lk;
}

static Xapian::MSet enquire_mset(struct req *req, Xapian::Enquire *enq)
{
	if (!req->max) {
		switch (sizeof(Xapian::doccount)) {
		case 4: req->max = UINT_MAX; break;
		default: req->max = ULLONG_MAX;
		}
	}
	for (int i = 0; i < 9; i++) {
		try {
			Xapian::MSet mset = enq->get_mset(req->off, req->max);
			return mset;
		} catch (const Xapian::DatabaseModifiedError & e) {
			AUTO_UNLOCK struct open_locks *lk =
							lock_shared_maybe(req);
			req->srch->db->reopen(); // may throw
		}
	}
	return enq->get_mset(req->off, req->max);
}

// for v1, v2, and extindex
static Xapian::MSet mail_mset(struct req *req, const char *qry_str)
{
	struct srch *srch = req->srch;
	Xapian::Query qry = srch->qp->parse_query(qry_str, srch->qp_flags);
	if (req->Oeidx_key) {
		req->Oeidx_key[0] = 'O'; // modifies static rbuf
		qry = Xapian::Query(Xapian::Query::OP_FILTER, qry,
					Xapian::Query(req->Oeidx_key));
	}
	// THREADID and UID are CPP macros defined by XapHelperCxx.pm
	if (req->uid_min != ULLONG_MAX && req->uid_max != ULLONG_MAX) {
		Xapian::Query range = Xapian::Query(
				Xapian::Query::OP_VALUE_RANGE, UID,
				Xapian::sortable_serialise(req->uid_min),
				Xapian::sortable_serialise(req->uid_max));
		qry = Xapian::Query(Xapian::Query::OP_FILTER, qry, range);
	}
	if (req->threadid != ULLONG_MAX) {
		std::string tid = Xapian::sortable_serialise(req->threadid);
		qry = Xapian::Query(Xapian::Query::OP_FILTER, qry,
			Xapian::Query(Xapian::Query::OP_VALUE_RANGE, THREADID,
					tid, tid));
	}
	Xapian::Enquire enq = prep_enquire(req);
	enq.set_query(qry);
	if (req->collapse_threads && has_threadid(srch))
		enq.set_collapse_key(THREADID);

	return enquire_mset(req, &enq);
}

static bool starts_with(const std::string *s, const char *pfx, size_t pfx_len)
{
	return s->size() >= pfx_len && !memcmp(pfx, s->c_str(), pfx_len);
}

static void apply_roots_filter(struct req *req, Xapian::Query *qry)
{
	if (!req->Pgit_dir) return;
	req->Pgit_dir[0] = 'P'; // modifies static rbuf
	Xapian::Database *xdb = req->srch->db;
	for (int i = 0; i < 9; i++) {
		try {
			std::string P = req->Pgit_dir;
			Xapian::PostingIterator p = xdb->postlist_begin(P);
			if (p == xdb->postlist_end(P)) {
				warnx("W: %s not indexed?", req->Pgit_dir + 1);
				return;
			}
			Xapian::TermIterator cur = xdb->termlist_begin(*p);
			Xapian::TermIterator end = xdb->termlist_end(*p);
			cur.skip_to("G");
			if (cur == end) {
				warnx("W: %s has no root commits?",
					req->Pgit_dir + 1);
				return;
			}
			Xapian::Query f = Xapian::Query(*cur);
			for (++cur; cur != end; ++cur) {
				std::string tn = *cur;
				if (!starts_with(&tn, "G", 1))
					continue;
				f = Xapian::Query(Xapian::Query::OP_OR, f, tn);
			}
			*qry = Xapian::Query(Xapian::Query::OP_FILTER, *qry, f);
			return;
		} catch (const Xapian::DatabaseModifiedError & e) {
			AUTO_UNLOCK struct open_locks *lk =
							lock_shared_maybe(req);
			xdb->reopen();
		}
	}
}

// for cindex
static Xapian::MSet commit_mset(struct req *req, const char *qry_str)
{
	struct srch *srch = req->srch;
	Xapian::Query qry = srch->qp->parse_query(qry_str, srch->qp_flags);
	apply_roots_filter(req, &qry);

	// we only want commits:
	qry = Xapian::Query(Xapian::Query::OP_FILTER, qry,
				Xapian::Query("T" "c"));
	Xapian::Enquire enq = prep_enquire(req);
	enq.set_query(qry);
	return enquire_mset(req, &enq);
}

static void emit_mset_stats(struct req *req, const Xapian::MSet *mset)
{
	if (req->fp[1])
		fprintf(req->fp[1], "mset.size=%llu nr_out=%zu\n",
			(unsigned long long)mset->size(), req->nr_out);
	else
		ABORT("BUG: %s caller only passed 1 FD", req->argv[0]);
}

static int my_setlinebuf(FILE *fp) // glibc setlinebuf(3) can't report errors
{
	return setvbuf(fp, NULL, _IOLBF, 0);
}

// n.b. __cleanup__ works fine with C++ exceptions, but not longjmp
// Only clang and g++ are supported, as AFAIK there's no other
// relevant Free(-as-in-speech) C++ compilers.
#define CLEANUP_FBUF __attribute__((__cleanup__(fbuf_ensure)))
static void fbuf_ensure(void *ptr)
{
	struct fbuf *fbuf = (struct fbuf *)ptr;
	if (fbuf->fp && fclose(fbuf->fp))
		err(EXIT_FAILURE, "fclose(fbuf->fp)"); // ENOMEM?
	fbuf->fp = NULL;
	free(fbuf->ptr);
}

static void fbuf_init(struct fbuf *fbuf)
{
	assert(!fbuf->ptr);
	fbuf->fp = open_memstream(&fbuf->ptr, &fbuf->len);
	if (!fbuf->fp) err(EXIT_FAILURE, "open_memstream(fbuf)");
}

static bool write_all(int fd, const struct fbuf *wbuf, size_t len)
{
	const char *p = wbuf->ptr;
	assert(wbuf->len >= len);
	do { // write to client FD
		ssize_t n = write(fd, p, len);
		if (n > 0) {
			len -= n;
			p += n;
		} else {
			perror(n ? "write" : "write (zero bytes)");
			return false;
		}
	} while (len);
	return true;
}

#define ERR_FLUSH(f) do { \
	if (ferror(f) | fflush(f)) err(EXIT_FAILURE, "ferror|fflush "#f); \
} while (0)

#define ERR_CLOSE(f, e) do { \
	if (ferror(f) | fclose(f)) \
		e ? err(e, "ferror|fclose "#f) : perror("ferror|fclose "#f); \
} while (0)

static size_t off2size(off_t n)
{
	if (n < 0 || (uintmax_t)n > SIZE_MAX)
		ABORT("off_t out of size_t range: %lld\n", (long long)n);
	return (size_t)n;
}

// for test usage only, we need to ensure the compiler supports
// __cleanup__ when exceptions are thrown
struct inspect { struct req *req; };

static void inspect_ensure(struct inspect *x)
{
	fprintf(x->req->fp[0], "pid=%d has_threadid=%d",
		(int)getpid(), has_threadid(x->req->srch) ? 1 : 0);
}

static bool cmd_test_inspect(struct req *req)
{
	__attribute__((__cleanup__(inspect_ensure))) struct inspect x;
	x.req = req;
	try {
		throw Xapian::InvalidArgumentError("test");
	} catch (Xapian::InvalidArgumentError) {
		return true;
	}
	fputs("this should not be printed", req->fp[0]);
	return false;
}

static bool cmd_test_sleep(struct req *req)
{
	for (;;) poll(NULL, 0, 10);
	return false;
}
#include "xh_mset.h" // read-only (WWW, IMAP, lei) stuff
#include "xh_cidx.h" // CodeSearchIdx.pm stuff

#define CMD(n) { .fn_len = sizeof(#n) - 1, .fn_name = #n, .fn = cmd_##n }
static const struct cmd_entry {
	size_t fn_len;
	const char *fn_name;
	cmd fn;
} cmds[] = { // should be small enough to not need bsearch || gperf
	// most common commands first
	CMD(mset), // WWW and IMAP requests
	CMD(dump_ibx), // many inboxes
	CMD(dump_roots), // per-cidx shard
	CMD(test_inspect), // least common commands last
	CMD(test_sleep), // least common commands last
};

#define MY_ARRAY_SIZE(x)	(sizeof(x)/sizeof((x)[0]))
#define RECV_FD_CAPA 3
#define RECV_FD_SPACE	(RECV_FD_CAPA * sizeof(int))
union my_cmsg {
	struct cmsghdr hdr;
	char pad[sizeof(struct cmsghdr) + 16 + RECV_FD_SPACE];
};

static bool io_to_rbuf_retry(int fd, int errnum, FILE *errfp)
{
	struct pollfd pfd;

	switch (errnum) {
	case EAGAIN:
		fputs("W: io_to_rbuf EAGAIN, unexpected\n", errfp);
		pfd.fd = fd;
		pfd.events = POLLIN;
		poll(&pfd, 1, -1);
		return true;
	case EINTR:
		return true;
	case ENOMEM: // read(3posix) documents ENOMEM + ENOBUFS
	case ENOBUFS:
		fprintf(errfp, "W: io_to_rbuf: %s, sleeping 100ms\n",
			strerror(errnum));
		poll(NULL, 0, 100);
		return true;
	default:
		fprintf(errfp, "E: io_to_rbuf: %s\n", strerror(errnum));
	}
	return false;
}

static void stderr_set(FILE *tmp_err)
{
#if STDERR_ASSIGNABLE
	if (my_setlinebuf(tmp_err))
		perror("W: setlinebuf(tmp_err)");
	stderr = tmp_err;
	return;
#endif
	int fd = fileno(tmp_err);
	if (fd < 0) err(EXIT_FAILURE, "BUG: fileno(tmp_err)");
	while (dup2(fd, STDERR_FILENO) < 0) {
		if (errno != EINTR)
			err(EXIT_FAILURE, "dup2(%d => 2)", fd);
	}
}

/*
 * clients may send a single NUL byte ("\0") as the command and
 * rely on req->fp[0] if it's readable since SOCK_SEQPACKET sockets
 * don't always allow gigantic messages in msghdr.msg_iov
 */
static bool io_to_rbuf(struct req *req, char *rbuf, size_t *len)
{
	ssize_t r;
	size_t off = 0;
	int fd = fileno(req->fp[0]); // regular file
	FILE *errfp = req->fp[2] ? req->fp[2] : stderr;
	if (!req->fp[1])
		errx(EXIT_FAILURE,
"no response FD received when getting 1-byte NUL input");

	do {
		r = read(fd, rbuf + off, *len - off);
	} while ( (r > 0 && (off += r) && off < *len) ||
		(r < 0 && io_to_rbuf_retry(fd, errno, errfp)) );
	if (r < 0) {
		for (size_t i = 0; req->fp[i]; i++)
			err(EXIT_FAILURE, "fclose(req->fp[%zu])", i);
		return false;
	} if (r == 0) {
		if (off) // success
			*len = off;
		else
			fputs("W: io_to_rbuf got no data\n", errfp);
	} else { // (r > 0)
		fprintf(errfp, "E: io_to_rbuf too much: off=%zu r=%zd\n",
			off, r);
	}
	ERR_CLOSE(req->fp[0], EXIT_FAILURE);
	size_t i = 0;
	do { req->fp[i] = req->fp[i + 1]; } while (req->fp[++i]);
	return true;
}

static bool is_reg_file(int fd) {
	struct stat sb;
	if (fstat(fd, &sb))
		errx(EXIT_FAILURE, "fstat(%d): ", fd);
	return !!S_ISREG(sb.st_mode);
}

static bool recv_req(struct req *req, char *rbuf, size_t *len)
{
	union my_cmsg cmsg = {};
	struct msghdr msg = {};
	struct iovec iov;
	ssize_t r;
	iov.iov_base = rbuf;
	iov.iov_len = *len;
	msg.msg_iov = &iov;
	msg.msg_iovlen = 1;
	msg.msg_control = &cmsg.hdr;
	msg.msg_controllen = CMSG_SPACE(RECV_FD_SPACE);

	// allow SIGTERM to hit
	CHECK(int, 0, sigprocmask(SIG_SETMASK, &workerset, NULL));

again:
	r = recvmsg(sock_fd, &msg, 0);
	if (r == 0) {
		exit(EX_NOINPUT); /* grandparent went away */
	} else if (r < 0) {
		switch (errno) {
		case EINTR: goto again;
		case EAGAIN: exit(0); // spurious wakeup for lei dynfork
		case EBADF: if (sock_fd < 0) exit(0);
			// fall-through
		default: err(EXIT_FAILURE, "recvmsg");
		}
	}

	// success! no signals for the rest of the request/response cycle
	CHECK(int, 0, sigprocmask(SIG_SETMASK, &fullset, NULL));
	if (r > 0 && msg.msg_flags & (MSG_CTRUNC|MSG_TRUNC))
		ABORT("recvmsg %zu => %zd trunc %d", *len, r, msg.msg_flags);

	enum input_state istate;
	istate = (r == 1 && *rbuf == '\0') ? IN_FILE_MAYBE : IN_RBUF;
	if (cmsg.hdr.cmsg_level == SOL_SOCKET &&
			cmsg.hdr.cmsg_type == SCM_RIGHTS) {
		size_t clen = cmsg.hdr.cmsg_len;
		int *fdp = (int *)CMSG_DATA(&cmsg.hdr);
		size_t i;
		for (i = 0; CMSG_LEN((i + 1) * sizeof(int)) <= clen; i++) {
			int fd = *fdp++;
			const char *mode = NULL;
			int fl = fcntl(fd, F_GETFL);
			if (fl == -1) {
				errx(EXIT_FAILURE, "invalid fd=%d", fd);
			} else if (fl & O_WRONLY) {
				mode = "w";
			} else if (fl & O_RDWR) {
				mode = "r+";
				if (i == 0 && is_reg_file(fd) &&
						istate == IN_FILE_MAYBE)
					istate = IN_FILE;
			} else {
				errx(EXIT_FAILURE,
					"invalid mode from F_GETFL: 0x%x", fl);
			}
			req->fp[i] = fdopen(fd, mode);
			if (!req->fp[i])
				err(EXIT_FAILURE, "fdopen(fd=%d)", fd);
		}
		if (istate == IN_FILE)
			return io_to_rbuf(req, rbuf, len);
		*len = r;
		return true;
	}
	errx(EXIT_FAILURE, "no FD received in %zd-byte request", r);
	return false;
}

static bool is_chert(const char *dir)
{
	char iamchert[PATH_MAX];
	struct stat sb;
	int rc = snprintf(iamchert, sizeof(iamchert), "%s/iamchert", dir);

	if (rc <= 0 || rc >= (int)sizeof(iamchert))
		err(EXIT_FAILURE, "BUG: snprintf(%s/iamchert)", dir);
	if (stat(iamchert, &sb) == 0 && S_ISREG(sb.st_mode))
		return true;
	return false;
}

static void srch_free(struct srch *srch)
{
	delete srch->qp;
	delete srch->db;
	free(srch);
}

static void srch_cache_renew(struct srch *keep)
{
	khint_t k;

	// can't delete while iterating, so just free each + clear
	for (k = kh_begin(srch_cache); k != kh_end(srch_cache); k++) {
		if (!kh_exist(srch_cache, k)) continue;
		struct srch *cur = kh_key(srch_cache, k);

		if (cur != keep)
			srch_free(cur);
	}
	srch_set_cs_clear(srch_cache);
	if (keep) {
		int absent;
		k = srch_set_put(srch_cache, keep, &absent);
		assert(absent);
		assert(k < kh_end(srch_cache));
	}
}

#include "xh_date.h" // GitDateRangeProcessor + GitDateFieldProcessor
#include "xh_thread_fp.h" // ThreadFieldProcessor

// setup query parser for altid and arbitrary headers
static void srch_init_extra(struct srch *srch, struct req *req)
{
	const char *XPFX;
	for (int i = 0; i < req->qpfxc; i++) {
		size_t len = strlen(req->qpfxv[i]);
		char *c = (char *)memchr(req->qpfxv[i], '=', len);

		if (c) { // it's boolean "gmane=XGMANE"
			XPFX = c + 1;
			*c = 0;
			srch->qp->add_boolean_prefix(req->qpfxv[i], XPFX);
			continue;
		}
		// maybe it's a non-boolean prefix "blob:XBLOBID"
		c = (char *)memchr(req->qpfxv[i], ':', len);
		if (!c)
			errx(EXIT_FAILURE, "bad -Q %s", req->qpfxv[i]);
		XPFX = c + 1;
		*c = 0;
		srch->qp->add_prefix(req->qpfxv[i], XPFX);
	}
}

static void srch_init(struct req *req)
{
	struct srch *srch = req->srch;
	const unsigned FLAG_PHRASE = Xapian::QueryParser::FLAG_PHRASE;
	srch->qp_flags = Xapian::QueryParser::FLAG_BOOLEAN |
			Xapian::QueryParser::FLAG_LOVEHATE |
			Xapian::QueryParser::FLAG_PURE_NOT |
			Xapian::QueryParser::FLAG_WILDCARD;
	long nfd = req->dirc * SHARD_COST;

	shard_nfd += nfd;
	if (shard_nfd > my_fd_max) {
		srch_cache_renew(srch);
		shard_nfd = nfd;
	}
	for (int retried = 0; retried < 2; retried++) {
		int i = 0;
		srch->qp_flags |= FLAG_PHRASE;
		try {
			AUTO_UNLOCK struct open_locks *lk =
							lock_shared_maybe(req);
			srch->db = new Xapian::Database(req->dirv[i]);
			if (!lei && is_chert(req->dirv[0]))
				srch->qp_flags &= ~FLAG_PHRASE;
			for (i = 1; i < req->dirc; i++) {
				const char *dir = req->dirv[i];
				if (!lei && srch->qp_flags & FLAG_PHRASE &&
						is_chert(dir))
					srch->qp_flags &= ~FLAG_PHRASE;
				srch->db->add_database(Xapian::Database(dir));
			}
			break;
		} catch (const Xapian::Error & e) {
			warnx("E: Xapian::Error: %s (%s)",
				e.get_description().c_str(), req->dirv[i]);
		} catch (...) { // does this happen?
			warn("E: add_database(%s)", req->dirv[i]);
		}
		if (retried) {
			errx(EXIT_FAILURE, "E: can't open %s", req->dirv[i]);
		} else {
			warnx("retrying...");
			if (srch->db)
				delete srch->db;
			srch->db = NULL;
			srch_cache_renew(srch);
		}
	}
	// these will raise and die on ENOMEM or other errors
	srch->qp = new Xapian::QueryParser;
	srch->qp->set_default_op(Xapian::Query::OP_AND);
	srch->qp->set_database(*srch->db);
	srch->qp->set_stemmer(Xapian::Stem("english"));
	srch->qp->set_stemming_strategy(Xapian::QueryParser::STEM_SOME);
	srch->qp->SET_MAX_EXPANSION(100);

	if (req->code_search) {
		qp_init_code_search(srch->qp); // CodeSearch.pm
	} else {
		qp_init_mail_search(srch->qp); // Search.pm
		srch->qp->add_boolean_prefix("thread", thread_fp);
		if (lei) {
			srch->qp->add_boolean_prefix("kw", "K");
			srch->qp->add_boolean_prefix("L", "L");
		}
	}
	srch_init_extra(req->srch, req);
}

#define OPT_U(ch, var, fn, max) do { \
	var = fn(optarg, &end, 10); \
	if (*end || var == max) ABORT("-"#ch" %s", optarg); \
} while (0)

static void dispatch(struct req *req)
{
	int c;
	size_t size = strlen(req->argv[0]);
	union {
		struct srch *srch;
		char *ptr;
	} kbuf;
	char *end;
	FILE *kfp;
	req->threadid = req->uid_min = req->uid_max = ULLONG_MAX;
	for (c = 0; c < (int)MY_ARRAY_SIZE(cmds); c++) {
		if (cmds[c].fn_len == size &&
			!memcmp(cmds[c].fn_name, req->argv[0], size)) {
			req->fn = cmds[c].fn;
			break;
		}
	}
	if (!req->fn) ABORT("not handled: `%s'", req->argv[0]);

	kfp = open_memstream(&kbuf.ptr, &size);
	if (!kfp) err(EXIT_FAILURE, "open_memstream(kbuf)");
	// write padding, first (contents don't matter)
	fwrite(&req->argv[0], offsetof(struct srch, ckey), 1, kfp);

	// global getopt variables:
	optopt = 0;
	optarg = NULL;
	MY_DO_OPTRESET();

	// XH_SPEC is generated from @PublicInbox::Search::XH_SPEC
	while ((c = getopt(req->argc, req->argv, XH_SPEC)) != -1) {
		switch (c) {
		case 'a': req->asc = true; break;
		case 'c': req->code_search = true; break;
		case 'd':
			req->dirv[req->dirc++] = optarg;
			if (MY_ARG_MAX == req->dirc) ABORT("too many -d");
			fprintf(kfp, "-d%c%s%c", 0, optarg, 0);
			break;
		case 'g': req->Pgit_dir = optarg - 1; break; // pad "P" prefix
		case 'k':
			req->sort_col = strtol(optarg, &end, 10);
			if (*end) ABORT("-k %s", optarg);
			switch (req->sort_col) {
			case LONG_MAX: case LONG_MIN: ABORT("-k %s", optarg);
			}
			break;
		case 'l':
			req->lockv[req->lockc++] = optarg;
			if (MY_ARG_MAX == req->lockc) ABORT("too many -l");
			break;
		case 'm': OPT_U(m, req->max, strtoull, ULLONG_MAX); break;
		case 'o': OPT_U(o, req->off, strtoull, ULLONG_MAX); break;
		case 'r': req->relevance = true; break;
		case 't': req->collapse_threads = true; break;
		case 'u': OPT_U(u, req->uid_min, strtoull, ULLONG_MAX); break;
		case 'A':
			req->pfxv[req->pfxc++] = optarg;
			if (MY_ARG_MAX == req->pfxc)
				ABORT("too many -A");
			break;
		case 'K': OPT_U(K, req->timeout_sec, strtoul, ULONG_MAX); break;
		case 'O': req->Oeidx_key = optarg - 1; break; // pad "O" prefix
		case 'T': OPT_U(T, req->threadid, strtoull, ULLONG_MAX); break;
		case 'U': OPT_U(U, req->uid_max, strtoull, ULLONG_MAX); break;
		case 'Q':
			req->qpfxv[req->qpfxc++] = optarg;
			if (MY_ARG_MAX == req->qpfxc) ABORT("too many -Q");
			fprintf(kfp, "-Q%c%s%c", 0, optarg, 0);
			break;
		default: ABORT("bad switch `-%c'", c);
		}
	}
	ERR_CLOSE(kfp, EXIT_FAILURE); // may ENOMEM, sets kbuf.srch
	kbuf.srch->db = NULL;
	kbuf.srch->qp = NULL;
	kbuf.srch->ckey_len = size - offsetof(struct srch, ckey);
	if (kbuf.srch->ckey_len <= 0 || !req->dirc)
		ABORT("no -d args (or too many)");

	int absent;
	khint_t ki = srch_set_put(srch_cache, kbuf.srch, &absent);
	assert(ki < kh_end(srch_cache));
	req->srch = kh_key(srch_cache, ki);
	if (absent) {
		srch_init(req);
	} else {
		assert(req->srch != kbuf.srch);
		srch_free(kbuf.srch);
		AUTO_UNLOCK struct open_locks *lk = lock_shared_maybe(req);
		req->srch->db->reopen();
	}
	if (req->timeout_sec)
		alarm(req->timeout_sec > UINT_MAX ?
			UINT_MAX : (unsigned)req->timeout_sec);
	cur_req = req; // set global for *FieldProcessor
	try {
		if (!req->fn(req))
			warnx("`%s' failed", req->argv[0]);
	} catch (const Xapian::Error & e) {
		warnx("Xapian::Error: %s", e.get_description().c_str());
	} catch (...) {
		warn("unhandled exception");
	}
	if (req->timeout_sec)
		alarm(0);
}

static void cleanup_pids(void)
{
	free(worker_pids);
	worker_pids = NULL;
}

static void stderr_restore(void)
{
#if STDERR_ASSIGNABLE
	stderr = orig_err;
	return;
#endif
	ERR_FLUSH(stderr);
	while (dup2(orig_err_fd, STDERR_FILENO) < 0) {
		if (errno != EINTR)
			err(EXIT_FAILURE, "dup2(%d => 2)", orig_err_fd);
	}
	clearerr(stderr);
}

static void sigw(int sig) // SIGTERM+SIGUSR1 handler for worker
{
	switch (sig) {
	case SIGUSR1: worker_needs_reopen = 1; break;
	default: sock_fd = -1; // break out of recv_loop
	}
}

#define CLEANUP_REQ __attribute__((__cleanup__(req_cleanup)))
static void req_cleanup(void *ptr)
{
	struct req *req = (struct req *)ptr;
	free(req->lenv);
	cur_req = NULL;
}

static void reopen_logs(void)
{
	if (stdout_path && *stdout_path && !freopen(stdout_path, "a", stdout))
		err(EXIT_FAILURE, "freopen %s", stdout_path);
	if (stderr_path && *stderr_path) {
		if (!freopen(stderr_path, "a", stderr))
			err(EXIT_FAILURE, "freopen %s", stderr_path);
		if (my_setlinebuf(stderr))
			err(EXIT_FAILURE, "setlinebuf(stderr)");
	}
}

static bool recv_once(void)
{
	static char rbuf[4096 * 33]; // per-process
	size_t len = sizeof(rbuf);
	CLEANUP_REQ struct req req = {};

	if (!recv_req(&req, rbuf, &len))
		return false;
	if (req.fp[1])
		stderr_set(req.fp[1]);

	// MY_ARG_MAX limits the return value of SPLIT2ARGV
	req.argc = (int)SPLIT2ARGV(req.argv, rbuf, len);
	dispatch(&req);
	ERR_CLOSE(req.fp[0], 0);
	if (req.fp[1]) {
		stderr_restore();
		ERR_CLOSE(req.fp[1], 0);
	}
	return true;
}

static void recv_loop(void) // worker process loop
{
	struct sigaction sa = {};
	sa.sa_handler = sigw;

	CHECK(int, 0, sigaction(SIGTERM, &sa, NULL));
	CHECK(int, 0, sigaction(SIGUSR1, &sa, NULL));

	while (sock_fd == 0) {
		if (!recv_once())
			continue;
		if (worker_needs_reopen) {
			worker_needs_reopen = 0;
			reopen_logs();
		}
	}
}

static void insert_pid(pid_t pid, unsigned nr)
{
	assert(!worker_pids[nr]);
	worker_pids[nr] = pid;
}

#define XSIGNAL(signame, handler) do { \
	if (signal(signame, handler) == SIG_ERR) \
		err(EXIT_FAILURE, "signal(" #signame ", " #handler ")"); \
} while (0)

static void start_worker(unsigned nr)
{
	pid_t pid = fork();
	if (pid < 0) {
		warn("E: fork(worker=%u)", nr);
	} else if (pid > 0) {
		insert_pid(pid, nr);
	} else {
		cleanup_pids();
		xclose(pipefds[0]);
		xclose(pipefds[1]);
		XSIGNAL(SIGCHLD, SIG_DFL);
		XSIGNAL(SIGTTIN, SIG_IGN);
		XSIGNAL(SIGTTOU, SIG_IGN);
		recv_loop();
		exit(0);
	}
}

static void start_workers(void)
{
	sigset_t old;

	CHECK(int, 0, sigprocmask(SIG_SETMASK, &fullset, &old));
	for (unsigned long nr = 0; nr < nworker; nr++) {
		if (!worker_pids[nr])
			start_worker(nr);
	}
	CHECK(int, 0, sigprocmask(SIG_SETMASK, &old, NULL));
}

static void cleanup_all(void)
{
	cleanup_pids();
	if (!srch_cache)
		return;
	srch_cache_renew(NULL);
	srch_set_destroy(srch_cache);
	srch_cache = NULL;
}

static void parent_reopen_logs(void)
{
	reopen_logs();
	for (unsigned long nr = nworker; nr < nworker_hwm; nr++) {
		pid_t pid = worker_pids[nr];
		if (pid != 0 && kill(pid, SIGUSR1))
			warn("BUG?: kill(%d, SIGUSR1)", (int)pid);
	}
}

static void sigp(int sig) // parent signal handler
{
	static const char eagain[] = "signals coming in too fast";
	static const char bad_sig[] = "BUG: bad sig\n";
	static const char write_errno[] = "BUG: sigp write (errno)";
	static const char write_zero[] = "BUG: sigp write wrote zero bytes";
	char c = 0;

	switch (sig) {
	case SIGCHLD: c = '.'; break;
	case SIGTTOU: c = '-'; break;
	case SIGTTIN: c = '+'; break;
	case SIGUSR1: c = '#'; break;
	default:
		write(STDERR_FILENO, bad_sig, sizeof(bad_sig) - 1);
		_exit(EXIT_FAILURE);
	}
	ssize_t w = write(pipefds[1], &c, 1);
	if (w > 0) return;
	if (w < 0 && errno == EAGAIN) {
		write(STDERR_FILENO, eagain, sizeof(eagain) - 1);
		return;
	} else if (w == 0) {
		write(STDERR_FILENO, write_zero, sizeof(write_zero) - 1);
	} else {
		// strerror isn't technically async-signal-safe, and
		// strerrordesc_np+strerrorname_np isn't portable
		write(STDERR_FILENO, write_errno, sizeof(write_errno) - 1);
	}
	_exit(EXIT_FAILURE);
}

static void reaped_prefork_worker(pid_t pid, int st)
{
	unsigned long nr = 0;
	for (; nr < nworker_hwm; nr++) {
		if (worker_pids[nr] == pid) {
			worker_pids[nr] = 0;
			break;
		}
	}
	if (nr >= nworker_hwm) {
		warnx("W: unknown pid=%d reaped $?=%d", (int)pid, st);
		return;
	}
	if (WIFEXITED(st) && WEXITSTATUS(st) == EX_NOINPUT)
		alive = false;
	else if (st)
		warnx("worker[%lu] died $?=%d alive=%d", nr, st, (int)alive);
	if (alive)
		start_workers();
}

static void reaped_dynfork_worker(pid_t pid, int st) // lei-only
{
	if (WIFEXITED(st) && WEXITSTATUS(st) == EX_NOINPUT)
		alive = false;
	else if (st)
		warnx("worker died $?=%d alive=%d", st, (int)alive);
}

static void do_sigchld(void)
{
	while (1) {
		int st;
		pid_t pid = waitpid(-1, &st, WNOHANG);

		if (pid > 0) {
			if (lei)
				reaped_dynfork_worker(pid, st);
			else
				reaped_prefork_worker(pid, st);
		} else if (pid == 0) {
			return;
		} else {
			switch (errno) {
			case ECHILD: return;
			case EINTR: break; // can it happen w/ WNOHANG?
			default: err(EXIT_FAILURE, "BUG: waitpid");
			}
		}
	}
}

static void do_sigttin(void)
{
	if (!alive) return;
	if (nworker >= WORKER_MAX) {
		warnx("workers cannot exceed %zu", (size_t)WORKER_MAX);
		return;
	}
	void *p = realloc(worker_pids, (nworker + 1) * sizeof(pid_t));
	if (!p) {
		warn("realloc worker_pids");
	} else {
		worker_pids = (pid_t *)p;
		worker_pids[nworker++] = 0;
		if (nworker_hwm < nworker)
			nworker_hwm = nworker;
		start_workers();
	}
}

static void do_sigttou(void)
{
	if (!alive || nworker <= 1) return;

	// worker_pids array does not shrink
	--nworker;
	for (unsigned long nr = nworker; nr < nworker_hwm; nr++) {
		pid_t pid = worker_pids[nr];
		if (pid != 0 && kill(pid, SIGTERM))
			warn("BUG?: kill(%d, SIGTERM)", (int)pid);
	}
}

static size_t living_workers(void)
{
	size_t ret = 0;

	for (unsigned long nr = 0; nr < nworker_hwm; nr++) {
		if (worker_pids[nr])
			ret++;
	}
	return ret;
}

static void prefork_loop(void)
{
	struct rlimit rl;

	if (getrlimit(RLIMIT_NOFILE, &rl))
		err(EXIT_FAILURE, "getrlimit");
	my_fd_max = rl.rlim_cur;
	if (my_fd_max < 72)
		warnx("W: RLIMIT_NOFILE=%ld too low\n", my_fd_max);
	my_fd_max -= 64;
	nworker_hwm = nworker;
	worker_pids = (pid_t *)xcalloc(nworker, sizeof(pid_t));

	start_workers();

	while (alive || living_workers()) {
		char sbuf[64];
		ssize_t n = read(pipefds[0], &sbuf, sizeof(sbuf));
		if (n < 0) {
			if (errno == EINTR) continue;
			err(EXIT_FAILURE, "read");
		} else if (n == 0) {
			errx(EXIT_FAILURE, "read EOF");
		}
		do_sigchld();
		for (ssize_t i = 0; i < n; i++) {
			switch (sbuf[i]) {
			case '.': break; // do_sigchld already called
			case '-': do_sigttou(); break;
			case '+': do_sigttin(); break;
			case '#': parent_reopen_logs(); break;
			default: errx(EXIT_FAILURE, "BUG: c=%c", sbuf[i]);
			}
		}
	}
}

static void xsetfl(int fd, int newflags)
{
	int fl = fcntl(fd, F_GETFL);
	if (fl == -1) err(EXIT_FAILURE, "F_GETFL");
	if (fcntl(fd, F_SETFL, fl | newflags))
		err(EXIT_FAILURE, "F_SETFL");
}

static void dynfork_dispatch(void) // lei-only
{
	sigset_t old;
	CHECK(int, 0, sigprocmask(SIG_SETMASK, &fullset, &old));
	pid_t pid = fork();
	if (pid < 0)
		err(EXIT_FAILURE, "fork");
	if (pid > 0) {
		CHECK(int, 0, sigprocmask(SIG_SETMASK, &old, NULL));
		return; // don't even care about the PID
	}
	if (pid == 0) {
		xclose(pipefds[0]);
		xclose(pipefds[1]);
		XSIGNAL(SIGCHLD, SIG_DFL);
		XSIGNAL(SIGTTIN, SIG_IGN);
		XSIGNAL(SIGTTOU, SIG_IGN);
		XSIGNAL(SIGUSR1, SIG_DFL);
		XSIGNAL(SIGTERM, SIG_DFL);
		(void)recv_once();
		exit(0);
	}
}

static void dynfork_check_sigs(void)
{
	char sbuf[64];
	ssize_t n = read(pipefds[0], &sbuf, sizeof(sbuf));
	if (n < 0) {
		if (errno == EAGAIN) return; // spurious wakeup
		err(EXIT_FAILURE, "read");
	} else if (n == 0) {
		errx(EXIT_FAILURE, "read EOF");
	}
	do_sigchld();
	for (ssize_t i = 0; i < n; i++) {
		switch (sbuf[i]) {
		case '.': break; // do_sigchld already called
		case '-': break; // ignore (TTOU|TTIN)
		case '+': break;
		case '#': reopen_logs(); break;
		default: errx(EXIT_FAILURE, "BUG: c=%c", sbuf[i]);
		}
	}
}

static void dynfork_loop(void) // for lei
{
	struct pollfd pfd[2];
	pfd[0].fd = sock_fd;
	pfd[1].fd = pipefds[0];
	pfd[0].events = pfd[1].events = POLLIN;

	xsetfl(pipefds[0], O_NONBLOCK);
	xsetfl(sock_fd, O_NONBLOCK);
	my_fd_max = 128; // just keep srch_init happy

	while (alive) {
		int rc = poll(pfd, MY_ARRAY_SIZE(pfd), -1);

		if (rc < 0) {
			if (errno == EINTR) continue;
			err(EXIT_FAILURE, "poll");
		} else {
			if (pfd[0].revents & POLLIN)
				dynfork_dispatch();
			if (pfd[1].revents & POLLIN)
				dynfork_check_sigs();
		}
	}
}

int main(int argc, char *argv[])
{
	int c;
	socklen_t slen = (socklen_t)sizeof(c);

	if (getsockopt(sock_fd, SOL_SOCKET, SO_TYPE, &c, &slen))
		err(EXIT_FAILURE, "getsockopt");
	if (c != SOCK_SEQPACKET)
		errx(EXIT_FAILURE, "stdin is not SOCK_SEQPACKET");

	stdout_path = getenv("STDOUT_PATH");
	stderr_path = getenv("STDERR_PATH");

	thread_fp = new ThreadFieldProcessor();
	xh_date_init();
	mail_rp_init();
	code_nrp_init();
	srch_cache = srch_set_init();
	atexit(cleanup_all);

	if (!STDERR_ASSIGNABLE) {
		orig_err_fd = dup(STDERR_FILENO);
		if (orig_err_fd < 0)
			err(EXIT_FAILURE, "dup(2)");
	}

	nworker = 1;
	// make warn/warnx/err multi-process friendly:
	if (my_setlinebuf(stderr))
		err(EXIT_FAILURE, "setlinebuf(stderr)");
	// not using -W<workers> like Daemon.pm, since -W is reserved (glibc)
	while ((c = getopt(argc, argv, "lj:")) != -1) {
		char *end;

		switch (c) {
		case 'j':
			nworker = strtoul(optarg, &end, 10);
			if (*end != 0 || nworker > WORKER_MAX)
				errx(EXIT_FAILURE, "-j %s invalid", optarg);
			break;
		case 'l':
			lei = true;
			break;
		case ':':
			errx(EXIT_FAILURE, "missing argument: `-%c'", optopt);
		case '?':
			errx(EXIT_FAILURE, "unrecognized: `-%c'", optopt);
		default:
			errx(EXIT_FAILURE, "BUG: `-%c'", c);
		}
	}
	sigset_t pset; // parent-only
	CHECK(int, 0, sigfillset(&pset));

	// global sigsets:
	CHECK(int, 0, sigfillset(&fullset));
	CHECK(int, 0, sigfillset(&workerset));

#define DELSET(sig) do { \
	CHECK(int, 0, sigdelset(&fullset, sig)); \
	CHECK(int, 0, sigdelset(&workerset, sig)); \
	CHECK(int, 0, sigdelset(&pset, sig)); \
} while (0)
	DELSET(SIGABRT);
	DELSET(SIGBUS);
	DELSET(SIGFPE);
	DELSET(SIGILL);
	DELSET(SIGSEGV);
	DELSET(SIGXCPU);
	DELSET(SIGXFSZ);
#undef DELSET
	CHECK(int, 0, sigdelset(&workerset, SIGUSR1));
	CHECK(int, 0, sigdelset(&fullset, SIGALRM));

	if (nworker == 0) { // no SIGTERM handling w/o workers
		recv_loop();
		return 0;
	}
	CHECK(int, 0, sigdelset(&workerset, SIGTERM));
	CHECK(int, 0, sigdelset(&workerset, SIGCHLD));

	if (pipe(pipefds)) err(EXIT_FAILURE, "pipe");
	xsetfl(pipefds[1], O_NONBLOCK);
	CHECK(int, 0, sigdelset(&pset, SIGCHLD));
	CHECK(int, 0, sigdelset(&pset, SIGTTIN));
	CHECK(int, 0, sigdelset(&pset, SIGTTOU));
	CHECK(int, 0, sigdelset(&pset, SIGUSR1));

	struct sigaction sa = {};
	sa.sa_handler = sigp;

	CHECK(int, 0, sigaction(SIGUSR1, &sa, NULL));
	CHECK(int, 0, sigaction(SIGTTIN, &sa, NULL));
	CHECK(int, 0, sigaction(SIGTTOU, &sa, NULL));
	sa.sa_flags = SA_NOCLDSTOP;
	CHECK(int, 0, sigaction(SIGCHLD, &sa, NULL));

	CHECK(int, 0, sigprocmask(SIG_SETMASK, &pset, NULL));
	if (lei)
		dynfork_loop();
	else
		prefork_loop();
	return 0;
}
