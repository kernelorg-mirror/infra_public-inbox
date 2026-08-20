# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# base class for remote IPC calls and workqueues, requires Storable or Sereal
# - ipc_do and ipc_worker_* is for a single worker/producer and uses pipes
# - wq_io_do and wq_worker* is for a single producer and multiple workers,
#   using SOCK_SEQPACKET for work distribution
# use ipc_do when you need work done on a certain process
# use wq_io_do when your work can be done on any idle worker
package PublicInbox::IPC;
use v5.12;
use parent qw(Exporter);
use autodie qw(close pipe read send socketpair);
use Errno qw(EAGAIN EINTR);
use Carp qw(croak carp);
use PublicInbox::Syscall qw(MY_SEQPACKET_MAX);
use PublicInbox::DS qw(awaitpid);
use PublicInbox::IO qw(my_bufread my_gets);
use PublicInbox::Spawn;
use PublicInbox::OnDestroy;
use PublicInbox::WQWorker;
use Socket qw(AF_UNIX SOCK_STREAM SOCK_SEQPACKET MSG_EOR);
use Scalar::Util qw(blessed reftype);

our @EXPORT_OK = qw(ipc_freeze ipc_thaw nproc_shards send_eor);
my ($enc, $dec);
# ->imports at BEGIN turns sereal_*_with_object into custom ops on 5.14+
# and eliminate method call overhead
BEGIN {
	eval {
		require Sereal::Encoder;
		require Sereal::Decoder;
		Sereal::Encoder->import('sereal_encode_with_object');
		Sereal::Decoder->import('sereal_decode_with_object');
		($enc, $dec) = (Sereal::Encoder->new, Sereal::Decoder->new);
	};
};

if ($enc && $dec) { # should be custom ops
	*ipc_freeze = sub ($) { sereal_encode_with_object $enc, $_[0] };
	*ipc_thaw = sub ($) { sereal_decode_with_object $dec, $_[0], my $ret };
} else {
	require Storable;
	*ipc_freeze = \&Storable::freeze;
	*ipc_thaw = \&Storable::thaw;
}

our ($recv_cmd, $send_cmd);
do {
	$recv_cmd = PublicInbox::Spawn->can('recv_cmd4');
	$send_cmd = PublicInbox::Spawn->can('send_cmd4');
} // do {
	require PublicInbox::Syscall;
	$recv_cmd = PublicInbox::Syscall->can('recv_cmd4');
	$send_cmd = PublicInbox::Syscall->can('send_cmd4');
};

sub _get_rec ($) {
	my ($r) = @_;
	my ($len, $bref);
	$len = my_gets($r) // croak "gets: $!";
	return if $len eq ''; # EOF
	chop($len) eq "\n" or croak "gets: no LF byte in <$len>";
	$bref = my_bufread($r, $len) or
		croak defined($bref) ? 'read EOF' : "bufread($len): $!";
	length($$bref) == $len or croak "bufread($len) short: ", length($$bref);
	ipc_thaw($$bref); # may croak
}

sub ipc_fail ($@) {
	my ($self, @msg) = @_;
	my @err = eval { ipc_worker_stop($self) };
	unshift @msg, @err;
	eval { delete $self->{-ipc_res} };
	unshift @msg, " (delete -ipc_res: $@)" if $@;
	croak @msg;
}

sub ipc_get_res ($) {
	my ($self) = @_;
	my $r = $self->{-ipc_res} // croak 'BUG: no {-ipc_res}';
	my $res = eval { _get_rec $r };
	ipc_fail $self, $@ if $@;
	$res;
}

sub ipc_read_step ($$) {
	my ($self, $inflight) = @_;
	croak 'BUG: -ipc_inflight too small' if @$inflight < 4;
	my ($sub, $sub_arg, $acb, $acb_arg) = @$inflight[0..3];
	my $ret = ipc_get_res $self;
	splice @$inflight, 0, 4;
	eval { $acb->($self, $sub, $sub_arg, $acb_arg, $ret) };
	return ($@ ? ($@) : ()) if wantarray;
	ipc_fail $self, "E: $sub $@" if $@;
}

sub _send_rec ($$) {
	my ($w, $ref) = @_;
	my $buf = ipc_freeze($ref);
	print $w length($buf), "\n", $buf or croak "print: $!";
}

sub ipc_req_async ($$) {
	my ($self, $ref) = @_;
	my $buf = ipc_freeze($ref);
	substr $buf, 0, 0, length($buf)."\n";
	my $inflight;
	while ($self->{-ipc_req}) {
		if (defined(my $w = syswrite $self->{-ipc_req}, $buf)) {
			return if $w == length($buf);
			substr $buf, 0, $w, ''; # sv_chop
		} elsif ($! != EAGAIN) {
			ipc_fail $self, "write: $!";
		}
		$inflight //= $self->{-ipc_inflight};
		ipc_read_step($self, $inflight) if @$inflight;
	}
	ipc_fail $self, '-ipc_req gone (closed in callback?)';
}

sub ipc_return ($$$) {
	my ($w, $ret, $exc) = @_;
	if ($exc) {
		# C/C++ exceptions from some XS|SWIG bindings have pointers
		# when serialized and will segfault if attempting to use
		# the deserialized result in a different address space, so
		# we stringify them:
		blessed($exc) && reftype($exc) eq 'SCALAR' and
			$exc = ref($exc).": $exc";
		$ret = bless \$exc, 'PublicInbox::IPC::Die';
	}
	_send_rec $w, $ret;
}

sub ipc_worker_loop ($$$) {
	my ($self, $r_req, $w_res) = @_;
	my ($rec, $wantarray, $sub, @args);
	while ($rec = _get_rec($r_req)) {
		($wantarray, $sub, @args) = @$rec;
		# no waiting if client doesn't care,
		# this is the overwhelmingly likely case
		if (!defined($wantarray)) {
			eval { $self->$sub(@args) };
			ipc_return($w_res, \undef, $@);
		} elsif ($wantarray) {
			my @ret = eval { $self->$sub(@args) };
			ipc_return($w_res, \@ret, $@);
		} else { # '' => wantscalar
			my $ret = eval { $self->$sub(@args) };
			ipc_return($w_res, \$ret, $@);
		}
	}
}

sub exit_exception { exit(!!$@) }

# starts a worker if Sereal or Storable is installed
sub ipc_worker_spawn {
	my ($self, $ident, $oldset, $fields, @cb_args) = @_;
	return if $self->{-ipc_res} && $self->{-ipc_res}->can_reap; # idempotent
	delete(@$self{qw(-ipc_req -ipc_res -ipc_inflight)});

	# n.b. we use 2 pipes here instead of a single socketpair since
	# Linux (as of v6.15) allows a 1MB pipe buffer but only 0.5MB
	# socket buffer for unprivileged processes.  The extra buffer
	# space improves parallel indexing performance by 5-10%
	pipe(my $r_req, my $w_req);
	pipe(my $r_res, my $w_res);
	my $sigset = $oldset // PublicInbox::DS::block_signals();
	$self->ipc_atfork_prepare;
	my $pid = PublicInbox::DS::fork_persist;
	if ($pid == 0) {
		delete @$self{qw(-wq_s1 -wq_s2 -wq_workers)};
		$w_req = $r_res = undef;
		$w_res->autoflush(1);
		$SIG{$_} = 'IGNORE' for (qw(TERM INT QUIT));
		local $0 = $ident;
		# ensure we properly exit even if warn() dies:
		my $end = on_destroy \&exit_exception;
		eval {
			$fields //= {};
			local @$self{keys %$fields} = values(%$fields);
			my $on_destroy = $self->ipc_atfork_child;
			local @SIG{keys %SIG} = values %SIG;
			PublicInbox::DS::sig_setmask($sigset);
			ipc_worker_loop($self, $r_req, $w_res);
		};
		warn "worker $ident PID:$$ died: $@\n" if $@;
		undef $end; # trigger exit
	}
	PublicInbox::DS::sig_setmask($sigset) unless $oldset;
	$r_req = $w_res = undef;
	$w_req->autoflush(1);
	my $inflight = $self->{-ipc_inflight} = [];
	$r_res->blocking(0);
	$w_req->blocking(0);
	$self->{-ipc_req} = $w_req;
	$self->{-ipc_res} = PublicInbox::IO::attach_pid($r_res, $pid,
				\&ipc_worker_reap, $self, $inflight, @cb_args);
	$pid; # used by tests
}

# n.b. we don't rely on {-ipc_inflight} and instead pass $inflight
# explicitly since we need to ensure $inflight is tied to the correct
# $pid and $self fields can be clobbered on respawn
sub ipc_worker_reap { # awaitpid callback
	my ($pid, $self, $inflight, $cb, @args) = @_;
	while (defined($inflight) && @$inflight) {
		my ($sub, $sub_arg, $acb, $acb_arg) = splice @$inflight, 0, 4;
		my $exc = bless \(my $x = "aborted\n"), 'PublicInbox::IPC::Die';
		eval { $acb->($self, $sub, $sub_arg, $acb_arg, $exc) };
		warn "E: (in abort): $sub: $@" if $@;
	}
	return $cb->($pid, $self, @args) if $cb;
	return if !$?;
	my $s = $? & 127;
	# TERM(15) is our default exit signal, PIPE(13) is likely w/ pager
	warn "$self->{-wq_ident} PID:$pid died \$?=$?\n" if $s != 15 && $s != 13
}

# for base class, override in sub classes
sub ipc_atfork_prepare {}

sub wq_atexit_child {}

sub ipc_atfork_child {
	my ($self) = @_;
	my $io = delete($self->{-ipc_atfork_child_close}) or return;
	close($_) for @$io;
	undef;
}

# idempotent, can be called regardless of whether worker is active or not
sub ipc_worker_stop {
	my ($self) = @_;
	if (my $w_req = delete $self->{-ipc_req}) {
		close $w_req; # invalidate if referenced upstack
		my @exc = ipc_wait_all $self;
		my $res = delete $self->{-ipc_res};
		return @exc if wantarray;
		die @exc if @exc;
		# ipc_worker_reap will fire for $res going out-of-scope
	}
	();
}

sub _wait_return ($$) {
	my ($r_res, $sub) = @_;
	my $ret = _get_rec($r_res) // die "no response on $sub";
	die $$ret if ref($ret) eq 'PublicInbox::IPC::Die';
	wantarray ? @$ret : $$ret;
}

my $ipc_die = sub { # default ipc_async acb
	my ($self, undef, undef, undef, $ret) = @_;
	if (ref($ret) eq 'PublicInbox::IPC::Die') {
		my @err = ("$$ret");
		push @err, (eval { ipc_worker_stop $self });
		push @err, $@ if $@;
		die @err;
	}
};

sub ipc_wait_all ($) {
	my ($self) = @_;
	my @exc;
	my $inflight = $self->{-ipc_inflight} // return @exc;
	while (@$inflight) {
		push @exc, ipc_read_step($self, $inflight);
	}
	croak(@exc) if @exc && !wantarray;
	@exc;
}

# call $self->$sub(@args), on a worker if ipc_worker_spawn was used
sub ipc_do {
	my ($self, $sub, @args) = @_;
	if ($self->{-ipc_req}) { # run in worker
		if (defined(wantarray)) {
			ipc_wait_all $self;
			ipc_req_async $self, [ wantarray, $sub, @args ];
			my $ret = ipc_get_res($self);
			die $$ret if ref($ret) eq 'PublicInbox::IPC::Die';
			wantarray ? @$ret : $$ret;
		} else { # likely, fire-and-forget into pipe, but dies async
			ipc_req_async $self, [ undef, $sub, @args ];
			push @{$self->{-ipc_inflight}}, $sub, \@args,
						$ipc_die, undef;
		}
	} else { # run locally
		$self->$sub(@args);
	}
}

sub ipc_async {
	my ($self, $sub, $sub_arg, $acb, $acb_arg) = @_;
	$sub_arg //= [];
	$acb //= $ipc_die;
	if ($self->{-ipc_req}) { # run in worker
		ipc_req_async $self, [ 1, $sub, @$sub_arg ];
		push @{$self->{-ipc_inflight}}, $sub, $sub_arg, $acb, $acb_arg;
	} else { # run locally
		my @ret = eval { $self->$sub(@$sub_arg) };
		my $exc = $@;
		my $ret = $exc ? bless(\$exc, 'PublicInbox::IPC::Die') : \@ret;
		$acb->($self, $sub, $sub_arg, $acb_arg, $ret);
		undef;
	}
}

# needed when there's multiple IPC workers and the parent forking
# causes newer siblings to inherit older siblings sockets
sub ipc_sibling_atfork_child {
	my ($self) = @_;
	my (undef, $res) = delete(@$self{qw(-ipc_req -ipc_res)});
	$res && $res->can_reap and
		die "BUG: $$ ipc_atfork_child called on itself";
}

sub recv_and_run {
	my ($self, $s2, $len, $full_stream) = @_;
	my @io = $recv_cmd->($s2, my $buf, $len // MY_SEQPACKET_MAX);
	return if scalar(@io) && !defined($io[0]);
	my $n = length($buf) or return 0;
	local @$self{0..$#io} = @io;
	$_->autoflush(1) for @io;
	while ($full_stream && $n < $len) {
		my $r = sysread($s2, $buf, $len - $n, $n);
		if ($r) {
			$n = length($buf); # keep looping
		} elsif (!defined $r) {
			if ($! == EAGAIN) {
				poll_in($s2)
			} elsif ($! != EINTR) {
				croak "sysread: $!";
			} # next on EINTR
		} else { # ($r == 0)
			croak "read EOF after $n/$len bytes";
		}
	}
	# Sereal dies on truncated data, Storable returns undef
	my $args = ipc_thaw($buf) // die "thaw error on buffer of size: $n";
	undef $buf;
	my $sub = shift @$args;
	eval { $self->$sub(@$args) };
	warn "$$ $0 wq_worker: $sub: $@" if $@;
	$n;
}

sub sock_defined { # PublicInbox::DS::post_loop_do CB
	my ($wqw) = @_;
	defined($wqw->{sock});
}

sub wq_worker_loop ($$$) {
	my ($self, $bcast2, $oldset) = @_;
	my $wqw = PublicInbox::WQWorker->new($self, $self->{-wq_s2});
	PublicInbox::WQWorker->new($self, $bcast2) if $bcast2;
	local @PublicInbox::DS::post_loop_do = (\&sock_defined, $wqw);
	my $sig = delete($self->{wq_sig});
	$sig->{CHLD} //= \&PublicInbox::DS::enqueue_reap;
	PublicInbox::DS::event_loop($sig, $oldset);
	PublicInbox::DS->Reset;
}

sub do_sock_stream { # via wq_io_do, for big requests
	my ($self, $len) = @_;
	recv_and_run($self, my $s2 = delete $self->{0}, $len, 1);
}

sub send_eor ($$) {
	my ($s) = @_;
	my $n;
	do { $n = send $s, $_[1], MSG_EOR } while !defined($n) && $! == EINTR;
	$n // ($! == EAGAIN ? return : croak("send: $!"));
	$n == length($_[1]) ? $n : croak('send('.length($_[1])." > $n)");
}

sub wq_broadcast {
	my ($self, $sub, @args) = @_;
	my $wkr = $self->{-wq_workers} or Carp::confess('no -wq_workers');
	my $buf = ipc_freeze([$sub, @args]);
	my $len = length($buf);
	carp "W: buffer of $len may be too large\n" if $len > 4096;
	my @exc; # we shouldn't get EAGAIN, here
	# FIXME: support retry on ENOBUFS for tiny systems
	for my $bcast1 (values %$wkr) {
		my $sock = $bcast1 // $self->{-wq_s1} // next;
		eval { send_eor($sock, $buf) } //
			push(@exc, $@ || "send: unexpected $!");
	}
	croak "@exc" if @exc;
}

sub sendmsg_eor ($$$;$) {
	my $n = $send_cmd->($_[0], $_[1], $_[2], MSG_EOR, $_[3] // 50) //
		return;
	$n == length($_[2]) ? $n : croak('sendmsg('.length($_[2])." > $n)");
}

sub stream_in_full ($$$) {
	my ($s1, $io, $buf) = @_;
	socketpair(my $r, my $w, AF_UNIX, SOCK_STREAM, 0);
	my $n = sendmsg_eor($s1, [ $r ],
			ipc_freeze(['do_sock_stream', length($buf)]))
		// croak "sendmsg: $!";
	undef $r;
	$n = $send_cmd->($w, $io, $buf, 0) // croak "sendmsg: $!";
	print $w substr($buf, $n) if $n < length($buf); # need > 2G on Linux
	close $w; # autodies if print failed
}

sub wq_io_do { # always async
	my ($self, $sub, $io, @args) = @_;
	my $s1 = $self->{-wq_s1} or Carp::confess('no -wq_s1');
	my $buf = ipc_freeze([$sub, @args]);
	if (length($buf) > MY_SEQPACKET_MAX) {
		stream_in_full($s1, $io, $buf);
	} elsif (defined sendmsg_eor($s1, $io, $buf)) {
		# success
	} else {
		$!{ETOOMANYREFS} and croak "sendmsg: $! (check RLIMIT_NOFILE)";
		$!{EMSGSIZE} ? stream_in_full($s1, $io, $buf) :
			croak("sendmsg: $!");
	}
}

sub wq_sync_run {
	my ($self, $wantarray, $sub, @args) = @_;
	if ($wantarray) {
		my @ret = eval { $self->$sub(@args) };
		ipc_return($self->{0}, \@ret, $@);
	} else { # '' => wantscalar
		my $ret = eval { $self->$sub(@args) };
		ipc_return($self->{0}, \$ret, $@);
	}
}

sub wq_do {
	my ($self, $sub, @args) = @_;
	if (defined(wantarray)) {
		pipe(my $r, my $w);
		wq_io_do($self, 'wq_sync_run', [ $w ], wantarray, $sub, @args);
		undef $w;
		_wait_return($r, $sub);
	} else {
		wq_io_do($self, $sub, [], @args);
	}
}

sub prepare_nonblock {
	($_[0]->{-wq_s1} // die 'BUG: no {-wq_s1}')->blocking(0);
	require PublicInbox::WQBlocked;
}

sub wq_nonblock_do { # always async
	my ($self, $sub, @args) = @_;
	my $buf = ipc_freeze([$sub, @args]);
	if ($self->{wqb}) { # saturated once, assume saturated forever
		$self->{wqb}->flush_send($buf);
	} elsif (defined sendmsg_eor($self->{-wq_s1}, [], $buf)) {
		# success!
	} elsif ($!{EAGAIN} || $!{ENOBUFS} || $!{ENOMEM}) {
		PublicInbox::WQBlocked->new($self, $buf);
	} else {
		croak "sendmsg: $!";
	}
}

sub _wq_worker_start {
	my ($self, $oldset, $fields, $one, @cb_args) = @_;
	my ($bcast1, $bcast2);
	$one or socketpair($bcast1, $bcast2, AF_UNIX, SOCK_SEQPACKET, 0);
	my $pid = PublicInbox::DS::fork_persist;
	if ($pid == 0) {
		undef $bcast1;
		delete $self->{-wq_s1};
		$self->{-wq_worker_nr} =
				keys %{delete($self->{-wq_workers}) // {}};
		$SIG{$_} = 'DEFAULT' for (qw(TTOU TTIN TERM QUIT INT CHLD));
		local $0 = $one ? $self->{-wq_ident} :
			"$self->{-wq_ident} $self->{-wq_worker_nr}";
		# ensure we properly exit even if warn() dies:
		my $end = on_destroy \&exit_exception;
		eval {
			$fields //= {};
			local @$self{keys %$fields} = values(%$fields);
			my $on_destroy = $self->ipc_atfork_child;
			local @SIG{keys %SIG} = values %SIG;
			wq_worker_loop($self, $bcast2, $oldset);
		};
		warn "worker $self->{-wq_ident} PID:$$ died: $@" if $@;
		undef $end; # trigger exit
	} elsif ($bcast1) {
		$self->{-wq_workers}->{$pid} = PublicInbox::IO::attach_pid(
			$bcast1, $pid,
			\&ipc_worker_reap, $self, undef, @cb_args);
	} else { # $one
		$self->{-wq_workers}->{$pid} = undef;
		awaitpid($pid, \&ipc_worker_reap, $self, undef, @cb_args);
	}
}

# starts workqueue workers if Sereal or Storable is installed
sub wq_workers_start {
	my ($self, $ident, $nr_workers, $oldset, $fields, @cb_args) = @_;
	($send_cmd && $recv_cmd) or return;
	return if $self->{-wq_s1}; # idempotent
	socketpair($self->{-wq_s1}, $self->{-wq_s2},AF_UNIX, SOCK_SEQPACKET, 0);
	$self->ipc_atfork_prepare;
	$nr_workers //= $self->{-wq_nr_workers}; # was set earlier
	my $sigset = $oldset // PublicInbox::DS::block_signals();
	$self->{-wq_workers} = {};
	$self->{-wq_ident} = $ident;
	my $one = $nr_workers == 1;
	$self->{-wq_nr_workers} = $nr_workers;
	for (1..$nr_workers) {
		_wq_worker_start($self, $sigset, $fields, $one, @cb_args);
	}
	PublicInbox::DS::sig_setmask($sigset) unless $oldset;
}

sub wq_close {
	my ($self) = @_;
	if (my $wqb = delete $self->{wqb}) {
		$wqb->enq_close;
	}
	delete @$self{qw(-wq_s1 -wq_s2 -wq_workers)};
}

sub wq_kill {
	my ($self, $sig) = @_;
	kill($sig // 'TERM', keys %{$self->{-wq_workers}});
}

sub DESTROY {
	my ($self) = @_;
	wq_close($self);
	ipc_worker_stop($self);
}

# _SC_NPROCESSORS_ONLN = 84 on both Linux glibc and musl,
# emitted using: $^X devel/sysdefs-list
my %NPROCESSORS_ONLN = (
	linux => 84,
	freebsd => 58,
	dragonfly => 58,
	openbsd => 503,
	netbsd => 1002
);

sub detect_nproc () {
	my $n = $NPROCESSORS_ONLN{$^O};
	return POSIX::sysconf($n) if defined $n;

	# getconf(1) is POSIX, but *NPROCESSORS* vars are not even if
	# glibc, {Free,Net,Open}BSD all support them.
	for (qw(_NPROCESSORS_ONLN NPROCESSORS_ONLN)) {
		`getconf $_ 2>/dev/null` =~ /^(\d+)$/ and return $1;
	}
	# note: GNU nproc(1) checks CPU affinity, which is nice but
	# isn't remotely portable
	undef
}

# SATA storage lags behind what CPUs are capable of, so relying on
# nproc(1) can be misleading and having extra Xapian shards is a
# waste of FDs and space.  It can also lead to excessive IO latency
# and slow things down.  Users on NVME or other fast storage can
# use the NPROC env or switches in our script/public-inbox-* programs
# to increase Xapian shards
our $NPROC_MAX_DEFAULT = 4;

sub nproc_shards ($) {
	my ($creat_opt) = @_;
	my $n = $creat_opt->{nproc} if ref($creat_opt) eq 'HASH';
	$n //= $ENV{NPROC};
	if (!$n) {
		# assume 2 cores if not detectable or zero
		state $NPROC_DETECTED = PublicInbox::IPC::detect_nproc() || 2;
		$n = $NPROC_DETECTED;
		$n = $NPROC_MAX_DEFAULT if $n > $NPROC_MAX_DEFAULT;
	}

	# subtract for the main process and git-fast-import
	$n -= 1;
	$n < 1 ? 1 : $n;
}

1;
