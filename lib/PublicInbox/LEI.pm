# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# Backend for `lei' (local email interface).  Unlike the C10K-oriented
# PublicInbox::Daemon, this is designed exclusively to handle trusted
# local clients with read/write access to the FS and use as many
# system resources as the local user has access to.
package PublicInbox::LEI;
use v5.12;
use parent qw(PublicInbox::DS PublicInbox::LeiExternal
	PublicInbox::LeiQuery);
use autodie qw(bind chdir listen open pipe socket socketpair syswrite unlink);
use Getopt::Long ();
use Socket qw(AF_UNIX SOCK_SEQPACKET pack_sockaddr_un);
use Errno qw(EPIPE EAGAIN ECONNREFUSED ENOENT ECONNRESET EINTR);
use Cwd qw(getcwd);
use POSIX qw(strftime);
use IO::Handle ();
use Fcntl qw(SEEK_SET);
use PublicInbox::Config;
use PublicInbox::Syscall qw(EPOLLIN);
use PublicInbox::Spawn qw(run_wait popen_rd run_qx);
use PublicInbox::DS qw(awaitpid);
eval { require PublicInbox::Lg2 }; # placate FindBin
use PublicInbox::Lock;
use PublicInbox::Eml;
use PublicInbox::Git qw(git_exe);
use PublicInbox::Import;
use PublicInbox::ContentHash qw(git_sha);
use PublicInbox::OnDestroy;
use PublicInbox::IPC qw(send_eor);
use PublicInbox::Search;
use PublicInbox::IO qw(poll_in read_all);
use PublicInbox::XapHelperCxx;
use Time::HiRes qw(stat); # ctime comparisons for config cache
use File::Path ();
use File::Spec;
use Carp qw(carp);
use Sys::Syslog qw(openlog syslog closelog);
our $quit = \&CORE::exit;
our ($current_lei, $errors_log, $listener, $oldset, $dir_idle);
my $GLP = Getopt::Long::Parser->new;
$GLP->configure(qw(gnu_getopt no_ignore_case auto_abbrev));
my $GLP_PASS = Getopt::Long::Parser->new;
$GLP_PASS->configure(qw(gnu_getopt no_ignore_case auto_abbrev pass_through));

our (%PATH2CFG, # persistent for socket daemon
$MDIR2CFGPATH, # location => { /path/to/config => [ ino watches ] }
$OPT, # shared between optparse and opt_dash callback (for Getopt::Long)
$daemon_pid
);

# TBD: this is a documentation mechanism to show a subcommand
# (may) pass options through to another command:
sub pass_through { $GLP_PASS }

sub opt_dash ($$) { # callback runs inside optparse
	my ($spec, $re_str) = @_; # 'limit|n=i', '([0-9]+)'
	my ($key) = ($spec =~ m/\A([a-z]+)/g);
	my $cb = sub { # Getopt::Long "<>" catch-all handler
		my ($arg) = @_;
		if ($arg =~ /\A-($re_str)\z/) {
			$OPT->{$key} = $1;
		} elsif ($arg eq '--') { # "--" arg separator, ignore first
			push @{$OPT->{-argv}}, $arg if $OPT->{'--'}++;
		# lone (single) dash is handled elsewhere
		} elsif (substr($arg, 0, 1) eq '-') {
			if ($OPT->{'--'}) {
				push @{$OPT->{-argv}}, $arg;
			} else {
				die "bad argument: $arg\n";
			}
		} else {
			push @{$OPT->{-argv}}, $arg;
		}
	};
	($spec, '<>' => $cb, $GLP_PASS) # for Getopt::Long
}

# rel2abs preserves symlinks in parent, unlike abs_path
sub rel2abs {
	my ($self, $p) = @_;
	if (index($p, '/') == 0) { # already absolute
		$p =~ tr!/!/!s; # squeeze redundant slashes
		chop($p) if substr($p, -1, 1) eq '/';
		return $p;
	}
	my $pwd = $self->{env}->{PWD};
	if (defined $pwd) {
		if (my @st_pwd = stat($pwd)) {
			my @st_cwd = stat($self->{3}) or die "stat({3}): $!";
			"@st_pwd[1,0]" eq "@st_cwd[1,0]" or
				$self->{env}->{PWD} = $pwd = undef;
		} else { # PWD was invalid
			$self->{env}->{PWD} = $pwd = undef;
		}
	}
	$pwd //= $self->{env}->{PWD} = getcwd() // die "getcwd: $!";
	File::Spec->rel2abs($p, $pwd);
}

# abs_path resolves symlinks in parent iff all parents exist
sub abs_path { Cwd::abs_path($_[1]) // rel2abs(@_) }

sub canonpath_harder {
	my $p = $_[-1]; # $_[0] may be self
	$p = File::Spec->canonpath($p);
	$p =~ m!(?:/*|\A)\.\.(?:/*|\z)! && -e $p ? Cwd::abs_path($p) : $p;
}

sub share_path ($) { # $HOME/.local/share/lei/$FOO
	my ($self) = @_;
	rel2abs($self, ($self->{env}->{XDG_DATA_HOME} //
		($self->{env}->{HOME} // '/nonexistent').'/.local/share')
		.'/lei');
}

sub store_path ($) { share_path($_[0]) . '/store' }

sub _config_path ($) {
	my ($self) = @_;
	rel2abs($self, ($self->{env}->{XDG_CONFIG_HOME} //
		($self->{env}->{HOME} // '/nonexistent').'/.config')
		.'/lei/config');
}

sub cache_dir ($) {
	my ($self) = @_;
	rel2abs($self, ($self->{env}->{XDG_CACHE_HOME} //
		($self->{env}->{HOME} // '/nonexistent').'/.cache')
		.'/lei');
}

sub url_folder_cache {
	my ($self) = @_;
	require PublicInbox::SharedKV; # URI => updated_at_sec_
	PublicInbox::SharedKV->new(cache_dir($self).'/uri_folder');
}

sub ale {
	my ($self) = @_;
	$self->{ale} // do {
		require PublicInbox::LeiALE;
		my $cfg = $self->_lei_cfg(1);
		$self->{ale} = $cfg->{ale} //= PublicInbox::LeiALE->new($self);
	};
}

sub index_opt {
	# TODO: drop underscore variants everywhere, they're undocumented
	qw(fsync|sync! jobs|j=i indexlevel|L=s compact
	max_size|max-size=s sequential-shard
	batch_size|batch-size=s skip-docdata)
}

my @c_opt = qw(c=s@ C=s@ quiet|q);
my @net_opt = (qw(no-torsocks torsocks=s), PublicInbox::LeiQuery::curl_opt());
my @lxs_opt = qw(remote! local! external! include|I=s@ exclude=s@ only|O=s@
	import-remote!);

# we don't support -C as an alias for --find-copies since it's already
# used for chdir
our @diff_opt = qw(unified|U=i output-indicator-new=s output-indicator-old=s
	output-indicator-context=s indent-heuristic!
	minimal patience histogram anchored=s@ diff-algorithm=s
	color-moved:s color-moved-ws=s no-color-moved no-color-moved-ws
	word-diff:s word-diff-regex=s color-words:s no-renames
	rename-empty! check ws-error-highlight=s full-index binary
	abbrev:i break-rewrites|B:s find-renames|M:s find-copies:s
	find-copies-harder irreversible-delete|D l=i diff-filter=s
	S=s G=s find-object=s pickaxe-all pickaxe-regex R
	relative:s text|a ignore-cr-at-eol ignore-space-at-eol
	ignore-space-change|b ignore-all-space|w ignore-blank-lines
	inter-hunk-context=i function-context|W exit-code ext-diff
	no-ext-diff textconv! src-prefix=s dst-prefix=s no-prefix
	line-prefix=s);

# we generate shell completion + help using %CMD and %OPTDESC,
# see lei__complete() and PublicInbox::LeiHelp
# command => [ positional_args, 1-line description, Getopt::Long option spec ]
our %CMD = ( # sorted in order of importance/use:
'q' => [ '--stdin|SEARCH_TERMS...', 'search for messages matching terms',
	'stdin|', # /|\z/ must be first for lone dash
	@lxs_opt, @net_opt,
	qw(save! output|mfolder|o=s format|f=s dedupe|d=s threads|t+
	thread-id|T=s
	sort|s=s reverse|r offset=i pretty jobs|j=s globoff|g augment|a
	import-before! lock=s@ rsyncable alert=s@ mua=s verbose|v+
	shared color! mail-sync!), @c_opt, opt_dash('limit|n=i', '[0-9]+') ],

'up' => [ 'OUTPUT...|--all', 'update saved search',
	qw(jobs|j=s lock=s@ alert=s@ mua=s verbose|v+ exclude=s@
	remote-fudge-time=s all:s remote! local! external!), @net_opt, @c_opt ],

'lcat' => [ '--stdin|MSGID_OR_URL...', 'display local copy of message(s)',
	'stdin|', # /|\z/ must be first for lone dash
	# some of these options are ridiculous for lcat
	@lxs_opt, @net_opt,
	qw(output|mfolder|o=s format|f=s dedupe|d=s threads|t+
	sort|s=s reverse|r offset=i jobs|j=s globoff|g augment|a
	import-before! lock=s@ rsyncable alert=s@ mua=s verbose|v+
	color!), @c_opt, opt_dash('limit|n=i', '[0-9]+') ],

'blob' => [ 'OID', 'show a git blob, reconstructing from mail if necessary',
	qw(git-dir=s@ cwd! verbose|v+ mail! oid-a|A=s path-a|a=s path-b|b=s),
	@lxs_opt, @net_opt, @c_opt ],

'rediff' => [ '--stdin|LOCATION...',
		'regenerate a diff with different options',
	'stdin|', # /|\z/ must be first for lone dash
	qw(git-dir=s@ cwd! verbose|v+ color:s no-color drq:1 dequote-only:1
	order-file=s), @diff_opt, @lxs_opt, @net_opt, @c_opt ],

'mail-diff' => [ '--stdin|LOCATION...', 'diff the contents of emails',
	'stdin|', # /|\z/ must be first for lone dash
	qw(verbose|v+ in-format|F=s color:s no-color raw-header),
	@diff_opt, @net_opt, @c_opt ],

'add-external' => [ 'LOCATION',
	'add/set priority of a publicinbox|extindex for extra matches',
	qw(boost=i mirror=s inbox-version=i epoch=s verbose|v+),
	@c_opt, index_opt(), @net_opt ],
'ls-external' => [ '[FILTER]', 'list publicinbox|extindex locations',
	qw(format|f=s z|0 globoff|g invert-match|v local remote), @c_opt ],
'ls-label' => [ '', 'list labels', qw(z|0 stats:s), @c_opt ],
'ls-mail-sync' => [ '[FILTER]', 'list mail sync folders',
		qw(z|0 globoff|g invert-match|v local remote), @c_opt ],
'ls-mail-source' => [ 'URL', 'list IMAP or NNTP mail source folders',
		qw(z|0 ascii l pretty url), @net_opt, @c_opt ],
'forget-external' => [ 'LOCATION...|--prune',
	'exclude further results from a publicinbox|extindex',
	qw(prune), @c_opt ],

'ls-search' => [ '[PREFIX]', 'list saved search queries',
		qw(format|f=s pretty l ascii z|0), @c_opt ],
'forget-search' => [ 'OUTPUT...|--prune', 'forget a saved search',
		qw(verbose|v+ prune:s), @c_opt ],
'edit-search' => [ 'OUTPUT', "edit saved search via `git config --edit'",
			@c_opt ],
'rm' => [ '--stdin|LOCATION...',
	'remove a message from the index and prevent reindexing',
	'stdin|', # /|\z/ must be first for lone dash
	qw(in-format|F=s lock=s@ commit-delay=i), @net_opt, @c_opt ],
'plonk' => [ '--threads|--from=IDENT',
	'exclude mail matching From: or threads from non-Message-ID searches',
	qw(stdin| threads|t from|f=s mid=s oid=s), @c_opt ],
tag => [ 'KEYWORDS... LOCATION...|--stdin',
	'set/unset keywords and/or labels on message(s)',
	qw(stdin| in-format|F=s input|i=s@ oid=s@ mid=s@ commit-delay=i),
	@net_opt, @c_opt, pass_through('-kw:foo for delete') ],

'purge-mailsource' => [ 'LOCATION|--all',
	'remove imported messages from IMAP, Maildirs, and MH',
	qw(exact! all jobs:i indexed), @c_opt ],

'add-watch' => [ 'LOCATION... [LABELS...]',
	'watch for new messages and flag changes',
	qw(poll-interval=s state=s recursive|r), @c_opt ],
'rm-watch' => [ 'LOCATION...', 'remove specified watch(es)',
	qw(recursive|r), @c_opt ],
'ls-watch' => [ '[FILTER...]', 'list active watches with numbers and status',
		qw(l z|0), @c_opt ],
'pause-watch' => [ '[WATCH_NUMBER_OR_FILTER]', qw(all local remote), @c_opt ],
'resume-watch' => [ '[WATCH_NUMBER_OR_FILTER]', qw(all local remote), @c_opt ],
'forget-watch' => [ '{WATCH_NUMBER|--prune}', 'stop and forget a watch',
	qw(prune), @c_opt ],

'reindex' => [ '', 'reindex all locally-indexed messages', @c_opt ],

'index' => [ 'LOCATION... [LABELS...]', 'one-time index from URL or filesystem',
	qw(in-format|F=s kw! offset=i recursive|r exclude=s include|I=s
	verbose|v+ incremental!), @net_opt, # mainly for --proxy=
	 @c_opt ],
import => [ 'LOCATION...|--stdin [LABELS...]',
	'one-time import/update from URL or filesystem',
	qw(stdin| offset=i recursive|r exclude=s include|I=s new-only
	lock=s@ in-format|F=s kw! verbose|v+ incremental! mail-sync!
	commit-delay=i sort|s:s@ noisy),
	@net_opt, @c_opt ],
'forget-mail-sync' => [ 'LOCATION...',
	'forget sync information for a mail folder', @c_opt ],
'refresh-mail-sync' => [ 'LOCATION...|--all',
	'prune dangling sync data for a mail folder', 'all:s',
		@net_opt, @c_opt ],
'export-kw' => [ 'LOCATION...|--all',
	'one-time export of keywords of sync sources',
	qw(all:s mode=s), @net_opt, @c_opt ],
'convert' => [ 'LOCATION...|--stdin',
	'one-time conversion from URL or filesystem to another format',
	qw(stdin| in-format|F=s out-format|f=s output|mfolder|o=s lock=s@ kw!
		rsyncable sort|s:s@),
	@net_opt, @c_opt ],
'p2q' => [ 'LOCATION_OR_COMMIT...|--stdin',
	"use a patch to generate a query for `lei q --stdin'",
	qw(stdin| in-format|F=s want|w=s@ uri debug), @net_opt, @c_opt ],
'config' => [ '[...]', sub {
		'git-config(1) wrapper for '._config_path($_[0]). "\n" .
	'-l/--list and other common git-config uses are supported'
	}, qw(config-file|system|global|file|f=s), # for conflict detection
	 qw(edit|e c=s@ C=s@), pass_through('git config') ],
'inspect' => [ 'ITEMS...|--stdin', 'inspect lei/store and/or local external',
	qw(stdin| pretty ascii dir|d=s), @c_opt ],

'init' => [ '[DIRNAME]', sub {
	"initialize storage, default: ".store_path($_[0]);
	}, @c_opt ],
'daemon-kill' => [ '[-SIGNAL]', 'signal the lei-daemon',
	# "-C DIR" conflicts with -CHLD, here, and chdir makes no sense, here
	opt_dash('signal|s=s', '[0-9]+|(?:[A-Z][A-Z0-9]+)') ],
'daemon-pid' => [ '', 'show the PID of the lei-daemon' ],
'help' => [ '[SUBCOMMAND]', 'show help' ],

# TODO
#'reorder-local-store-and-break-history' => [ '[REFNAME]',
#	'rewrite git history in an attempt to improve compression',
#	qw(gc!), @c_opt ],
#'fuse-mount' => [ 'PATHNAME', 'expose lei/store as Maildir(s)', @c_opt ],
#
# internal commands are prefixed with '_'
'_complete' => [ '[...]', 'internal shell completion helper',
		pass_through('everything') ],
); # @CMD

# switch descriptions, try to keep consistent across commands
# $spec: Getopt::Long option specification
# $spec => [@ALLOWED_VALUES (default is first), $description],
# $spec => $description
# "$SUB_COMMAND TAB $spec" => as above
my $stdin_formats = [ 'MAIL_FORMAT|eml|mboxrd|mboxcl2|mboxcl|mboxo',
			'specify message input format' ];
my $ls_format = [ 'OUT|plain|json|null', 'listing output format' ];
my $sort_out = [ 'VAL|received|relevance|docid',
		"order of results is `--output'-dependent"];
my $sort_in = [ 'sequence|mtime|size', 'sort input (format-dependent)' ];

# we use \x{a0} (non-breaking SP) to avoid wrapping in PublicInbox::LeiHelp
my %OPTDESC = (
'help|h' => 'show this built-in help',
'c=s@' => [ 'NAME=VALUE', 'set config option' ],
'C=s@' => [ 'DIR', 'chdir to specify to directory' ],
'quiet|q' => 'be quiet',
'lock=s@' => [ 'METHOD|dotlock|fcntl|flock|none',
	'mbox(5) locking method(s) to use (default: fcntl,dotlock)' ],

'incremental!	import' => 'import already seen IMAP and NNTP articles',
'globoff|g' => "do not match locations using '*?' wildcards ".
		"and\xa0'[]'\x{a0}ranges",
'invert-match|v' => 'select non-matching lines',
'color!' => 'disable color (for --format=text)',
'verbose|v+' => 'be more verbose',
'external!' => 'do not use externals',
'mail!' => 'do not look in mail storage for OID',
'cwd!' => 'do not look in git repo of current working directory',
'oid-a|A=s' => 'pre-image OID',
'path-a|a=s' => 'pre-image pathname associated with OID',
'path-b|b=s' => 'post-image pathname associated with OID',
'git-dir=s@' => 'additional git repository to scan',
'dir|d=s	inspect' =>
	'specify a inboxdir, extindex topdir or Xapian shard',
'proxy=s' => [ 'PROTO://HOST[:PORT]', # shared with curl(1)
	"proxy for (e.g. `socks5h://0:9050')" ],
'torsocks=s' => ['VAL|auto|no|yes',
		'whether or not to wrap git and curl commands with torsocks'],
'no-torsocks' => 'alias for --torsocks=no',
'save!' =>  "do not save a search for `lei up'",
'import-remote!' => 'do not memoize remote messages into local store',
'import-before!' => 'do not import before writing to output (DANGEROUS)',

'type=s' => [ 'any|mid|git', 'disambiguate type' ],

'dedupe|d=s' => ['STRATEGY|content|oid|mid|none',
		'deduplication strategy'],
'threads|t+' =>
	'return all messages in the same threads as the actual match(es)',

'want|w=s@' => [ 'PREFIX|dfpost|dfn', # common ones in help...
		'search prefixes to extract (default: dfpost7)' ],
'uri	p2q' => [ 'URI escape output' ],

'alert=s@' => ['CMD,:WINCH,:bell,<any command>',
	'run command(s) or perform ops when done writing to output ' .
	'(default: ":WINCH,:bell" with --mua and Maildir/IMAP output, ' .
	'nothing otherwise)' ],

'augment|a' => 'augment --output destination instead of clobbering',

'output|mfolder|o=s' => [ 'MFOLDER',
	"destination (e.g.\xa0`/path/to/Maildir', ".
	"or\xa0`-'\x{a0}for\x{a0}stdout)" ],
'mua=s' => [ 'CMD',
	"MUA to run on --output Maildir or mbox (e.g.\xa0`mutt\xa0-f\xa0%f')" ],
'new-only	import' => 'only import new messages from IMAP source',

'inbox-version=i' => [ 'NUM|1|2',
		'force a public-inbox version with --mirror'],
'mirror=s' => [ 'URL', 'mirror a public-inbox'],

# public-inbox-index options
'fsync!' => 'speed up indexing after --mirror, risk index corruption',
'compact' => 'run compact index after mirroring',
'indexlevel|L=s' => [ 'LEVEL|full|medium|basic',
	"indexlevel with --mirror (default: full)" ],
'max_size|max-size=s' => [ 'SIZE',
	'do not index messages larger than SIZE (default: infinity)' ],
'batch_size|batch-size=s' => [ 'SIZE',
	'flush changes to OS after given number of bytes (default: 1m)' ],
'sequential-shard' =>
	'index Xapian shards sequentially for slow storage',
'skip-docdata' =>
	'drop compatibility w/ public-inbox <1.6 to save ~1.5% space',

'format|f=s	q' => [
	'OUT|maildir|mboxrd|mboxcl2|mboxcl|mboxo|html|json|jsonl|concatjson',
		'specify output format, default depends on --output'],
'exclude=s@	q' => [ 'LOCATION',
		'exclude specified external(s) from search' ],
'include|I=s@	q' => [ 'LOCATION',
		'include specified external(s) in search' ],
'only|O=s@	q' => [ 'LOCATION',
		'only use specified external(s) for search' ],
'jobs|j=s' => [ 'JOBSPEC',
		'control number of query and writer jobs' .
		"integers delimited by `,', either of which may be omitted"
		],
'jobs|j=i	add-external' => 'set parallelism when indexing after --mirror',

'in-format|F=s' => $stdin_formats,
'format|f=s	ls-search' => ['OUT|json|jsonl|concatjson',
			'listing output format' ],
'l	ls-search' => 'long listing format',
'l	ls-watch' => 'long listing format',
'l	ls-mail-source' => 'long listing format',
'url	ls-mail-source' => 'show full URL of newsgroup or IMAP folder',
'format|f=s	ls-external' => $ls_format,

'prune:s	forget-search' =>
	['TYPE|local|remote', 'prune all, remote or local folders' ],

'limit|n=i@' => ['NUM', 'limit on number of matches (default: 10000)' ],
'offset=i' => ['OFF', 'search result offset (default: 0)'],

'sort|s=s	q' => $sort_out,
'sort|s=s	lcat' => $sort_out,
'sort|s:s@	convert' => $sort_in,
'sort|s:s@	import' => $sort_in,
'reverse|r' => 'reverse search results', # like sort(1)

'boost=i' => 'increase/decrease priority of results (default: 0)',

'local' => 'limit operations to the local filesystem',
'local!' => 'exclude results from the local filesystem',
'remote' => 'limit operations to those requiring network access',
'remote!' => 'prevent operations requiring network access',

# up, refresh-mail-sync, export-kw
'all:s' => ['TYPE|local|remote', 'all remote or local folders' ],

'remote-fudge-time=s' => [ 'INTERVAL',
	'look for mail INTERVAL older than the last successful query' ],

'mid=s' => 'specify the Message-ID of a message',
'oid=s' => 'specify the git object ID of a message',

'recursive|r' => 'scan directories/mailboxes/newsgroups recursively',
'exclude=s' => 'exclude mailboxes/newsgroups based on pattern',
'include=s' => 'include mailboxes/newsgroups based on pattern',

'exact' => 'operate on exact header matches only',
'exact!' => 'rely on content match instead of exact header matches',

'by-mid|mid:s' => [ 'MID', 'match only by Message-ID, ignoring contents' ],

'kw!' => 'disable/enable importing keywords (aka "flags")',

# xargs, env, use "-0", git(1) uses "-z".  We support z|0 everywhere
'z|0' => 'use NUL \\0 instead of newline (CR) to delimit lines',

'signal|s=s' => [ 'SIG', 'signal to send lei-daemon (default: TERM)' ],
'edit|e	config' => 'open an editor to modify the lei config file',
); # %OPTDESC

my %CONFIG_KEYS = (
	'leistore.dir' => 'top-level storage location',
);

my @WQ_KEYS = qw(lxs l2m ikw pmd wq1 lne v2w); # internal workers

sub _drop_wq {
	my ($self) = @_;
	for my $wq (grep(defined, delete(@$self{@WQ_KEYS}))) {
		$wq->wq_kill(-POSIX::SIGTERM());
		$wq->DESTROY;
	}
}

sub send_gently ($$) { eval { send_eor $_[0], $_[1] } }

# pronounced "exit": x_it(1 << 8) => exit(1); x_it(13) => SIGPIPE
sub x_it ($$) {
	my ($self, $code) = @_;
	# make sure client sees stdout before exit
	$self->{1}->autoflush(1) if $self->{1};
	stop_pager($self);
	if ($self->{pkt_op_p}) { # worker => lei-daemon
		$self->{pkt_op_p}->pkt_do('x_it', $code);
		exit($code >> 8) if $$ != $daemon_pid;
	} elsif ($self->{sock}) { # lei->daemon => lei(1) client
		send_gently $self->{sock}, "x_it $code";
	} elsif ($quit == \&CORE::exit) { # an admin (one-shot) command
		exit($code >> 8);
	} # else ignore if client disconnected
	$self->dclose if $$ == $daemon_pid;
}

sub err ($;@) {
	my $self = shift;
	my $err = $self->{2} // ($self->{pgr} // [])->[2] // \*STDERR;
	my @eor = (substr($_[-1]//'', -1, 1) eq "\n" ? () : ("\n"));
	print $err @_, @eor and return;
	my $old_err = delete $self->{2};
	$old_err->close if $! == EPIPE && $old_err;
	$err = $self->{2} = ($self->{pgr} // [])->[2] // \*STDERR;
	print $err @_, @eor or print STDERR @_, @eor;
}

sub qerr ($;@) { $_[0]->{opt}->{quiet} or err(shift, @_) }

sub qfin { # show message on finalization (LeiFinmsg)
	my ($lei, $msg) = @_;
	return if $lei->{opt}->{quiet};
	$lei->{fmsg} ? push(@{$lei->{fmsg}}, "$msg\n") : qerr($lei, $msg);
}

sub fail_handler ($;$$) {
	my ($lei, $code, $io) = @_;
	$io->close if $io; # needed to avoid warnings on SIGPIPE
	_drop_wq($lei);
	x_it($lei, $code // (1 << 8));
}

sub sigpipe_handler { # handles SIGPIPE from @WQ_KEYS workers
	fail_handler($_[0], 13, delete $_[0]->{1});
}

sub fail ($;@) {
	my ($lei, @msg) = @_;
	my $exit_code = ($msg[0]//'') =~ /\A-?[0-9]+\z/ ? shift(@msg) : undef;
	local $current_lei = $lei;
	$lei->{failed}++;
	if (@msg) {
		push @msg, "\n" if substr($msg[-1], -1, 1);
		warn @msg;
	}
	$lei->{pkt_op_p}->pkt_do('fail_handler') if $lei->{pkt_op_p};
	x_it($lei, $exit_code // (1 << 8));
	undef;
}

sub out ($;@) {
	my $self = shift;
	return if print { $self->{1} // return } @_; # likely
	return note_sigpipe($self, 1) if $! == EPIPE;
	my $err = "error writing to output: $!";
	delete $self->{1};
	fail($self, $err);
}

sub puts ($;@) { out(shift, map { "$_\n" } @_) }

sub child_error { # passes non-fatal curl exit codes to user
	my ($self, $child_error, $msg) = @_; # child_error is $?
	local $current_lei = $self;
	$child_error ||= 1 << 8;
	warn(substr($msg, -1, 1) eq "\n" ? $msg : "$msg\n") if defined $msg;
	$self->{child_error} ||= $child_error;
	if ($self->{pkt_op_p}) { # to top lei-daemon
		$self->{pkt_op_p}->pkt_do('child_error', $child_error);
	} elsif ($self->{sock}) { # to lei(1) client
		send_gently $self->{sock}, "child_error $child_error";
	} # else noop if client disconnected
}

sub note_sigpipe { # triggers sigpipe_handler
	my ($self, $fd) = @_;
	delete($self->{$fd})->close; # explicit close silences Perl warning
	$self->{pkt_op_p}->pkt_do('sigpipe_handler') if $self->{pkt_op_p};
	x_it($self, 13);
}

my $term_handler = sub { exit(128 + 15) };

sub _lei_atfork_child {
	my ($self, $persist) = @_;
	# we need to explicitly close things which are on stack
	my $cfg = $self->{cfg};
	delete @$cfg{qw(-watches -lei_note_event)};
	if ($persist) {
		open $self->{3}, '<', '/';
		fchdir($self);
		close($_) for (grep(defined, delete @$self{qw(0 1 2 sock)}));
		delete $cfg->{-lei_store};
	} else { # worker, Net::NNTP (Net::Cmd) uses STDERR directly
		open STDERR, '+>&='.fileno($self->{2}); # idempotent w/ fileno
		STDERR->autoflush(1);
		$self->{2} = \*STDERR;
		POSIX::setpgid(0, $$) // die "setpgid(0, $$): $!";
	}
	close($_) for (grep(defined, delete @$self{qw(old_1 au_done)}));
	close($_) for (@{delete($self->{-socks}) // []});
	if (my $op_c = delete $self->{pkt_op_c}) {
		close(delete $op_c->{sock});
	}
	if (my $pgr = delete $self->{pgr}) {
		close($_) for (@$pgr[1,2]);
	}
	close $listener if $listener;
	undef $listener;
	$dir_idle->force_close if $dir_idle;
	undef $dir_idle;
	%PATH2CFG = ();
	$MDIR2CFGPATH = undef;
	eval 'no warnings; undef $PublicInbox::LeiNoteEvent::to_flush';
	undef $errors_log;
	$quit = \&CORE::exit;
	$self->{opt}->{noisy} or # only "lei import" sets this atm
		$SIG{__WARN__} = PublicInbox::Eml::warn_ignore_cb();
	$SIG{TERM} = $term_handler;
	$current_lei = $persist ? undef : $self; # for SIG{__WARN__}
}

sub _delete_pkt_op { # OnDestroy callback to prevent leaks on die
	my ($self) = @_;
	if (my $op = delete $self->{pkt_op_c}) { # in case of die
		$op->close; # PublicInbox::PktOp::close
	}
	my $pkt_op_p = delete($self->{pkt_op_p}) or return;
	close $pkt_op_p->{op_p};
}

sub pkt_op_pair {
	my ($self) = @_;
	require PublicInbox::PktOp;
	my $end = on_destroy \&_delete_pkt_op, $self;
	@$self{qw(pkt_op_c pkt_op_p)} = PublicInbox::PktOp->pair;
	$end;
}

sub incr {
	my $lei = shift;
	$lei->{incr_pid} = $$ if @_;
	while (my ($f, $n) = splice(@_, 0, 2)) { $lei->{$f} += $n }
}

sub pkt_ops {
	my ($lei, $ops) = @_;
	$ops->{fail_handler} = [ $lei ];
	$ops->{sigpipe_handler} = [ $lei ];
	$ops->{x_it} = [ $lei ];
	$ops->{child_error} = [ $lei ];
	$ops->{incr} = [ $lei ];
	$ops;
}

sub workers_start {
	my ($lei, $wq, $jobs, $ops, $flds) = @_;
	$ops //= {};
	($wq->can('net_merge_all_done') && $lei->{auth}) and
		$lei->{auth}->op_merge($ops, $wq, $lei);
	pkt_ops($lei, $ops);
	$ops->{''} //= [ $wq->can('_lei_wq_eof') || \&wq_eof, $lei ];
	my $end = $lei->pkt_op_pair;
	my $ident = $wq->{-wq_ident} // "lei-$lei->{cmd} worker";
	$flds->{lei} = $lei;
	$wq->wq_workers_start($ident, $jobs, $lei->oldset, $flds,
		$wq->can('_wq_done_wait') // \&wq_done_wait, $lei);
	delete $lei->{pkt_op_p};
	my $op_c = delete $lei->{pkt_op_c};
	@$end = ();
	$lei->event_step_init;
	($op_c, $ops);
}

# call this when we're ready to wait on events and yield to other clients
sub wait_wq_events {
	my ($lei, $op_c, $ops) = @_;
	my $wq1 = $lei->{wq1};
	($wq1 && $wq1->can('net_merge_all_done') && !$lei->{auth}) and
		$wq1->net_merge_all_done;
	for my $wq (grep(defined, @$lei{qw(ikw pmd)})) { # auxiliary WQs
		$wq->wq_close;
	}
	$wq1->{lei_sock} = $lei->{sock} if $wq1;
	$op_c->{ops} = $ops;
}

sub wq1_start {
	my ($lei, $wq, $jobs) = @_;
	my ($op_c, $ops) = workers_start($lei, $wq, $jobs // 1);
	$lei->{wq1} = $wq;
	wait_wq_events($lei, $op_c, $ops); # net_merge_all_done if !{auth}
}

sub _help {
	require PublicInbox::LeiHelp;
	PublicInbox::LeiHelp::call($_[0], $_[1], \%CMD, \%OPTDESC);
}

sub optparse ($$$) {
	my ($self, $cmd, $argv) = @_;
	# allow _complete --help to complete, not show help
	return 1 if substr($cmd, 0, 1) eq '_';
	$self->{cmd} = $cmd;
	local $OPT = $self->{opt} //= {};
	my $info = $CMD{$cmd} // [ '[...]' ];
	my ($proto, undef, @spec) = @$info;
	my $glp = ref($spec[-1]) eq ref($GLP) ? pop(@spec) : $GLP;
	push @spec, qw(help|h);
	my $lone_dash;
	if ($spec[0] =~ s/\|\z//s) { # "stdin|" or "clear|" allows "-" alias
		$lone_dash = $spec[0];
		$OPT->{$spec[0]} = \(my $var);
		push @spec, '' => \$var;
	}
	$glp->getoptionsfromarray($argv, $OPT, @spec) or
		return _help($self, "bad arguments or options for $cmd");
	return _help($self) if $OPT->{help};

	push @$argv, @{$OPT->{-argv}} if defined($OPT->{-argv});

	# "-" aliases "stdin" or "clear"
	$OPT->{$lone_dash} = ${$OPT->{$lone_dash}} if defined $lone_dash;

	if ($proto =~ s/\s*\[?(?:KEYWORDS|LABELS)\.\.\.\]?\s*//g) {
		require PublicInbox::LeiInput;
		my @err = PublicInbox::LeiInput::vmd_mod_extract($self, $argv);
		return $self->fail(join("\n", @err)) if @err;
	}

	my $i = 0;
	my $POS_ARG = '[A-Z][A-Z0-9_]+';
	my ($err, $inf);
	my @args = split(/ /, $proto);
	for my $var (@args) {
		if ($var =~ /\A$POS_ARG\.\.\.\z/o) { # >= 1 args;
			$inf = defined($argv->[$i]) and last;
			$var =~ s/\.\.\.\z//;
			$err = "$var not supplied";
		} elsif ($var =~ /\A$POS_ARG\z/o) { # required arg at $i
			$argv->[$i++] // ($err = "$var not supplied");
		} elsif ($var =~ /\.\.\.\]\z/) { # optional args start
			$inf = 1;
			last;
		} elsif ($var =~ /\A\[-?$POS_ARG\]\z/) { # one optional arg
			$i++;
		} elsif ($var =~ /\A.+?\|/) { # required FOO|--stdin
			$inf = 1 if index($var, '...') > 0;
			my @or = split(/\|/, $var);
			my $ok;
			for my $o (@or) {
				if ($o =~ /\A--([a-z0-9\-]+)/) {
					my $sw = $1;
					# assume pipe/regular file on stdin
					# w/o args means stdin
					if ($sw eq 'stdin' && !@$argv &&
							(-p $self->{0} ||
							 -f _)) {
						$OPT->{stdin} //= 1;
					}
					$ok = defined($OPT->{$sw}) and last;
				} elsif (defined($argv->[$i])) {
					$ok = 1;
					$i++;
					last;
				} # else continue looping
			}
			last if $ok;
			my $last = pop @or;
			$err = join(', ', @or) . " or $last must be set";
		} else {
			warn "BUG: can't parse `$var' in $proto";
		}
		last if $err;
	}
	if (!$inf && scalar(@$argv) > scalar(@args)) {
		$err //= 'too many arguments';
	}
	$err ? fail($self, "usage: lei $cmd $proto\nE: $err") : 1;
}

sub lazy_cb ($$$) { # $pfx is _complete_ or lei_
	my ($self, $cmd, $pfx) = @_;
	my $ucmd = $cmd;
	$ucmd =~ tr/-/_/;
	my $cb;
	$cb = $self->can($pfx.$ucmd) and return $cb;
	my $base = $ucmd;
	$base =~ s/_([a-z])/\u$1/g;
	my $pkg = "PublicInbox::Lei\u$base";
	($INC{"PublicInbox/Lei\u$base.pm"} // eval("require $pkg")) ?
		$pkg->can($pfx.$ucmd) : undef;
}

sub do_env {
	my $lei = shift;
	fchdir($lei);
	my $cb = shift // return ($lei, %{$lei->{env}}) ;
	local ($current_lei, %ENV) = ($lei, %{$lei->{env}});
	$cb = $lei->can($cb) if !ref($cb); # $cb may be a scalar sub name
	eval { $cb->($lei, @_) };
	$lei->fail($@) if $@;
}

sub dispatch {
	my ($self, $cmd, @argv) = @_;
	local ($current_lei, %ENV) = do_env($self);
	$self->{2}->autoflush(1); # keep stdout buffered until x_it|DESTROY
	return _help($self, 'no command given') unless defined($cmd);
	# do not support Getopt bundling for this
	while ($cmd eq '-C' || $cmd eq '-c') {
		my $v = shift(@argv) // return fail($self, $cmd eq '-C' ?
					'-C DIRECTORY' : '-c <name>=<value>');
		push @{$self->{opt}->{substr($cmd, 1, 1)}}, $v;
		$cmd = shift(@argv) // return _help($self, 'no command given');
	}
	if (my $cb = lazy_cb(__PACKAGE__, $cmd, 'lei_')) {
		optparse($self, $cmd, \@argv) or return;
		if (my $chdir = $self->{opt}->{C}) {
			for my $d (@$chdir) {
				next if $d eq ''; # same as git(1)
				chdir $d;
			}
			open($self->{3}, '<', '.');
		}
		$cb->($self, @argv);
	} elsif (grep(/\A-/, $cmd, @argv)) { # --help or -h only
		$GLP->getoptionsfromarray([$cmd, @argv], {}, qw(help|h C=s@))
			or return _help($self, 'bad arguments or options');
		_help($self);
	} else {
		fail($self, "`$cmd' is not an lei command");
	}
}

sub _lei_cfg ($;$) {
	my ($self, $creat) = @_;
	return $self->{cfg} if $self->{cfg};
	my $f = _config_path($self);
	my @st = stat($f);
	my $cur_st = @st ? pack('dd', $st[10], $st[7]) : ''; # 10:ctime, 7:size
	my ($sto, $sto_dir, $watches, $lne, $cfg);
	if ($cfg = $PATH2CFG{$f}) { # reuse existing object in common case
		($cur_st eq $cfg->{-st} && !$self->{opt}->{c}) and
			return ($self->{cfg} = $cfg);
		# reuse some fields below if they match:
		($sto, $sto_dir, $watches, $lne) =
				@$cfg{qw(-lei_store leistore.dir -watches
					-lei_note_event)};
	}
	if (!@st) {
		unless ($creat) { # any commands which write to cfg must creat
			$cfg = PublicInbox::Config->git_config_dump(
							'/dev/null', $self);
			return ($self->{cfg} = $cfg);
		}
		my ($cfg_dir) = ($f =~ m!(.*?/)[^/]+\z!);
		File::Path::mkpath($cfg_dir);
		open my $fh, '>>', $f;
		@st = stat($fh) or die "fstat($f): $!\n";
		$cur_st = pack('dd', $st[10], $st[7]);
		qerr($self, "# $f created") if $self->{cmd} ne 'config';
	}
	$cfg = PublicInbox::Config->git_config_dump($f, $self);
	$cfg->{-st} = $cur_st;
	if ($sto && canonpath_harder($sto_dir // store_path($self))
			eq canonpath_harder($cfg->{'leistore.dir'} //
						store_path($self))) {
		$cfg->{-lei_store} = $sto;
		$cfg->{-lei_note_event} = $lne;
		$cfg->{-watches} = $watches if $watches;
	}
	if (scalar(keys %PATH2CFG) > 5) {
		# FIXME: use inotify/EVFILT_VNODE to detect unlinked configs
		delete(@PATH2CFG{grep(!-f, keys %PATH2CFG)});
	}
	$self->{cfg} = $self->{opt}->{c} ? $cfg : ($PATH2CFG{$f} = $cfg);
	refresh_watches($self);
	$cfg;
}

sub _lei_store ($;$) {
	my ($self, $creat) = @_;
	my $cfg = _lei_cfg($self, $creat) // return;
	$cfg->{-lei_store} //= do {
		require PublicInbox::LeiStore;
		my $dir = $cfg->{'leistore.dir'} // store_path($self);
		return unless $creat || -d $dir;
		PublicInbox::LeiStore->new($dir, { creat => $creat });
	};
}

# returns true on success, undef
# argv[0] eq `+e' means errors do not ->fail # (like `sh +e')
sub _config {
	my ($self, @argv) = @_;
	my $err_ok = ($argv[0] // '') eq '+e' ? shift(@argv) : undef;
	my %env;
	my %opt = map { $_ => $self->{$_} } (0..2);
	my $cfg = _lei_cfg($self, 1);
	my $opt_c = delete local $cfg->{-opt_c};
	my @file_arg;
	if ($opt_c) {
		my ($set, $get, $nondash);
		for (@argv) { # order matters for git-config
			if (!$nondash) {
				if (/\A--(?:add|rename-section|remove-section|
						replace-all|
						unset-all|unset)\z/x) {
					++$set;
				} elsif ($_ eq '-l' || $_ eq '--list' ||
						/\A--get/) {
					++$get;
				} elsif (/\A-/) { # -z and such
				} else {
					++$nondash;
				}
			} else {
				++$nondash;
			}
		}
		if ($set || ($nondash//0) > 1 && !$get) {
			@file_arg = ('-f', $cfg->{-f});
			$env{GIT_CONFIG} = $file_arg[1];
		} else { # OK, we can use `-c n=v' for read-only
			$cfg->{-opt_c} = $opt_c;
			$env{GIT_CONFIG} = undef;
		}
	}
	my $cmd = $cfg->config_cmd(\%env, \%opt);
	push @$cmd, @file_arg, @argv;
	run_wait($cmd, \%env, \%opt) ? ($err_ok ? undef : fail($self, $?)) : 1;
}

sub lei_daemon_pid { puts shift, $daemon_pid }

sub lei_daemon_kill {
	my ($self) = @_;
	my $sig = $self->{opt}->{signal} // 'TERM';
	kill($sig, $$) or fail($self, "kill($sig, $$): $!");
}

# Shell completion helper.  Used by lei-completion.bash and hopefully
# other shells.  Try to do as much here as possible to avoid redundancy
# and improve maintainability.
sub lei__complete {
	my ($self, @argv) = @_; # argv = qw(lei and any other args...)
	shift @argv; # ignore "lei", the entire command is sent
	@argv or return puts $self, grep(!/^_/, keys %CMD), qw(--help -h -C);
	my $cmd = shift @argv;
	my $info = $CMD{$cmd} // do { # filter matching commands
		@argv or puts $self, grep(/\A\Q$cmd\E/, keys %CMD);
		return;
	};
	my ($proto, undef, @spec) = @$info;
	my $cur = pop @argv;
	my $re = defined($cur) ? qr/\A\Q$cur\E/ : qr/./;
	if (substr(my $_cur = $cur // '-', 0, 1) eq '-') { # --switches
		# gross special case since the only git-config options
		# Consider moving to a table if we need more special cases
		# we use Getopt::Long for are the ones we reject, so these
		# are the ones we don't reject:
		if ($cmd eq 'config') {
			puts $self, grep(/$re/, keys %CONFIG_KEYS);
			@spec = qw(add z|null get get-all unset unset-all
				replace-all get-urlmatch
				remove-section rename-section
				name-only list|l edit|e
				get-color-name get-colorbool);
			# fall-through
		}
		# generate short/long names from Getopt::Long specs
		puts $self, grep(/$re/, qw(--help -h -C), map {
			if (s/[:=].+\z//) { # req/optional args, e.g output|o=i
			} elsif (s/\+\z//) { # verbose|v+
			} elsif (s/!\z//) {
				# negation: mail! => no-mail|mail
				s/([\w\-]+)/$1|no-$1/g
			}
			map {
				my $x = length > 1 ? "--$_" : "-$_";
				$x eq $_cur ? () : $x;
			} grep(!/_/, split(/\|/, $_, -1)) # help|h
		} grep { $OPTDESC{"$_\t$cmd"} || $OPTDESC{$_} } @spec);
	} elsif ($cmd eq 'config' && !@argv && !$CONFIG_KEYS{$cur}) {
		puts $self, grep(/$re/, keys %CONFIG_KEYS);
	}

	# switch args (e.g. lei q -f mbox<TAB>)
	if (($argv[-1] // $cur // '') =~ /\A--?([\w\-]+)\z/) {
		my $opt = quotemeta $1;
		puts $self, map {
			my $v = $OPTDESC{$_};
			my @v = ref($v) ? split(/\|/, $v->[0]) : ();
			# get rid of ALL CAPS placeholder (e.g "OUT")
			# (TODO: completion for external paths)
			shift(@v) if scalar(@v) && uc($v[0]) eq $v[0];
			@v;
		} grep(/\A(?:[\w-]+\|)*$opt\b.*?(?:\t$cmd)?\z/, keys %OPTDESC);
	}
	if (my $cb = lazy_cb($self, $cmd, '_complete_')) {
		puts $self, $cb->($self, @argv, $cur ? ($cur) : ());
	}
	# TODO: URLs, pathnames, OIDs, MIDs, etc...  See optparse() for
	# proto parsing.
}

sub exec_buf ($$) {
	my ($argv, $env) = @_;
	my $argc = scalar @$argv;
	my $buf = 'exec '.join("\0", scalar(@$argv), @$argv);
	while (my ($k, $v) = each %$env) { $buf .= "\0$k=$v" };
	$buf;
}

sub start_mua {
	my ($self) = @_;
	if ($self->{ovv}->{fmt} =~ /\A(?:maildir)\z/) { # TODO: IMAP
		refresh_watches($self);
	}
	my $mua = $self->{opt}->{mua} // return;
	my $mfolder = $self->{ovv}->{dst};
	my (@cmd, $replaced);
	if ($mua =~ /\A(?:mutt|mailx|mail|neomutt)\z/) {
		@cmd = ($mua, '-f');
	# TODO: help wanted: other common FOSS MUAs
	} else {
		require Text::ParseWords;
		@cmd = Text::ParseWords::shellwords($mua);
		# mutt uses '%f' for open-hook with compressed mbox, we follow
		@cmd = map { $_ eq '%f' ? ($replaced = $mfolder) : $_ } @cmd;
	}
	push @cmd, $mfolder unless defined($replaced);
	if ($self->{sock}) { # lei(1) client process runs it
		# restore terminal: echo $query | lei q --stdin --mua=...
		my $io = [];
		$io->[0] = $self->{1} if $self->{opt}->{stdin} && -t $self->{1};
		send_exec_cmd($self, $io, \@cmd, {});
	}

	# kick wait_startq:
	syswrite($self->{au_done}, 'q') if $self->{lxs} && $self->{au_done};

	return unless -t $self->{2}; # XXX how to determine non-TUI MUAs?
	$self->{opt}->{quiet} = 1;
	delete $self->{-progress};
	delete $self->{opt}->{verbose};
}

sub send_exec_cmd { # tell script/lei to execute a command
	my ($self, $io, $cmd, $env) = @_;
	PublicInbox::IPC::sendcmd_eor(
			$self->{sock} // die('lei client gone'),
			$io, exec_buf($cmd, $env)) //
		Carp::croak("sendmsg: $!");
}

sub poke_mua { # forces terminal MUAs to wake up and hopefully notice new mail
	my ($self) = @_;
	my $alerts = $self->{opt}->{alert} // return;
	my $sock = $self->{sock};
	while (my $op = shift(@$alerts)) {
		if ($op eq ':WINCH') {
			# hit the process group that started the MUA
			send_gently $sock, '-WINCH' if $sock;
		} elsif ($op eq ':bell') {
			out($self, "\a");
		} elsif ($op =~ /(?<!\\),/) { # bare ',' (not ',,')
			push @$alerts, split(/(?<!\\),/, $op);
		} elsif ($op =~ m!\A([/a-z0-9A-Z].+)!) {
			my $cmd = $1; # run an arbitrary command
			require Text::ParseWords;
			$cmd = [ Text::ParseWords::shellwords($cmd) ];
			send_gently $sock, exec_buf($cmd, {}) if $sock;
		} else {
			warn("W: unsupported --alert=$op\n"); # non-fatal
		}
	}
}

my %path_to_fd = ('/dev/stdin' => 0, '/dev/stdout' => 1, '/dev/stderr' => 2);
$path_to_fd{"/dev/fd/$_"} = $_ for (0..2);

# this also normalizes the path
sub path_to_fd {
	my ($self, $path) = @_;
	$path = rel2abs($self, $path);
	$path =~ tr!/!/!s;
	$path_to_fd{$path} // (
		($path =~ m!\A/(?:dev|proc/self)/fd/[0-9]+\z!) ?
			fail($self, "cannot open $path from daemon") : -1
	);
}

# caller needs to "-t $self->{1}" to check if tty
sub start_pager {
	my ($self, $new_env) = @_;
	chomp(my $pager = run_qx([git_exe, qw(var GIT_PAGER)]));
	warn "`git var PAGER' error: \$?=$?" if $?;
	return if $pager eq 'cat' || $pager eq '';
	$new_env //= {};
	$new_env->{LESS} //= 'FRX';
	$new_env->{LV} //= '-c';
	$new_env->{MORE} = $new_env->{LESS} if $^O eq 'freebsd';
	my $rdr = { 1 => $self->{1}, 2 => $self->{2} };
	CORE::pipe($rdr->{0}, my $wpager) or return warn "pipe: $!";
	my $pgr = [ undef, @$rdr{1, 2} ];
	my $env = $self->{env};
	if ($self->{sock}) { # lei(1) process runs it
		delete @$new_env{keys %$env}; # only set iff unset
		send_exec_cmd($self, [ @$rdr{0..2} ], [$pager], $new_env);
	} else {
		die 'BUG: start_pager w/o socket';
	}
	$self->{1} = $wpager;
	$self->{2} = $wpager if -t $self->{2};
	$env->{GIT_PAGER_IN_USE} = 'true'; # we may spawn git
	$self->{pgr} = $pgr;
}

# display a message for user before spawning full-screen $VISUAL
sub pgr_err {
	my ($self, @msg) = @_;
	return warn(@msg) unless $self->{sock} && -t $self->{2};
	start_pager($self, { LESS => 'RX' }); # no 'F' so we prompt
	say { $self->{2} } @msg, '# -quit pager to continue-';
	$self->{2}->autoflush(1);
	stop_pager($self);
	send_gently $self->{sock}, 'wait'; # wait for user to quit pager
}

sub stop_pager {
	my ($self) = @_;
	my $pgr = delete($self->{pgr}) or return;
	$self->{2} = $pgr->[2];
	delete($self->{1})->close if $self->{1};
	$self->{1} = $pgr->[1];
}

sub accept_dispatch { # Listener {post_accept} callback
	my ($sock) = @_; # ignore other
	$sock->autoflush(1);
	my $self = bless { sock => $sock }, __PACKAGE__;
	my (@io, $buf);
	do {
		poll_in $sock, 60_000 or return send_gently $sock,
						'timed out waiting to recv FDs';
		@io = PublicInbox::IPC::recvcmd_eor($sock, $buf) or return;
	} while (!defined($io[0]) && $! == EAGAIN);
	if (!defined($io[0])) {
		warn(my $msg = "recvcmd failed: $!");
		return send_gently $sock, $msg;
	} elsif (@io == 4) {
		@$self{0..$#io} = @io;
	} else {
		return send_gently $sock, 'wrong # of FDs='.scalar(@io);
	}
	# $ENV_STR = join('', map { "\0$_=$ENV{$_}" } keys %ENV);
	# $buf = "$argc\0".join("\0", @ARGV).$ENV_STR."\0\0";
	substr($buf, -2, 2, '') eq "\0\0" or  # s/\0\0\z//
		return send_gently $sock, 'request command truncated';
	my ($argc, @argv) = split(/\0/, $buf, -1);
	undef $buf;
	my %env = map { split(/=/, $_, 2) } splice(@argv, $argc);
	$self->{env} = \%env;
	eval { dispatch($self, @argv) };
	$self->fail($@) if $@;
}

sub dclose {
	my ($self) = @_;
	local $current_lei = $self;
	delete $self->{-progress};
	_drop_wq($self) if $self->{failed};
	$self->close if $self->{-event_init_done}; # PublicInbox::DS::close
}

sub _drop_sto_long {
	my ($self) = @_;
	my $reqid = delete $self->{-long_reqid} or return;
	($self->{sto} // return)->wq_do('abort_long_req', $reqid);
}

sub long_reqid {
	my ($self) = @_;
	$self->{-long_reqid} // do {
		my @st = stat $self->{sock} or die "stat(lei->{sock}): $!";
		# n.b. inode may be recycled by kernel, so prefix with time
		$self->{-long_reqid} = PublicInbox::DS::now.".$st[1]";
	};
}

# for long-running results from script/lei
sub event_step {
	my ($self) = @_;
	local %ENV = %{$self->{env}};
	local $current_lei = $self;
	eval {
		my @io = PublicInbox::IPC::recvcmd_eor($self->{sock} // return,
							my $buf, 4096);
		if (scalar(@io) == 1 && !defined($io[0])) {
			return if $! == EAGAIN;
			die "recvmsg: $!" if $! != ECONNRESET;
			@io = (); # for open loop below:
		}
		if ($buf eq '') {
			_drop_wq($self); # EOF, client disconnected
			dclose($self);
			_drop_sto_long($self);
			$buf = 'TERM';
		}
		if ($buf =~ /\A(?:STOP|CONT|TERM)\z/) {
			my $sig = "-$buf";
			for my $wq (grep(defined, @$self{@WQ_KEYS})) {
				$wq->wq_kill($sig);
			}
		} else {
			die "unrecognized client signal: $buf";
		}
		my $s = $self->{-socks} // []; # lei up --all
		@$s = grep { send_gently $_, $buf } @$s;
	};
	if (my $err = $@) {
		eval { $self->fail($err) };
		dclose($self);
	}
}

sub event_step_init {
	my ($self) = @_;
	my $sock = $self->{sock} or return;
	$self->{-event_init_done} // do { # persist til $ops done
		$sock->blocking(0);
		$self->SUPER::new($sock, EPOLLIN);
		$self->{-event_init_done} = $sock;
	};
}

sub oldset { $oldset }

sub dump_and_clear_log {
	if (defined($errors_log) && -s STDIN && seek(STDIN, 0, SEEK_SET)) {
		openlog('lei-daemon', 'pid,nowait,nofatal,ndelay', 'user');
		chomp(my @lines = <STDIN>);
		truncate(STDIN, 0) or
			syslog('warning', "ftruncate (%s): %m", $errors_log);
		for my $l (@lines) { syslog('warning', '%s', $l) }
		closelog(); # don't share across fork
	}
}

sub cfg2lei ($) {
	my ($cfg) = @_;
	my $lei = bless { env => { %{$cfg->{-env}} } }, __PACKAGE__;
	open($lei->{0}, '<&', \*STDIN);
	open($lei->{1}, '>>&', \*STDOUT);
	open($lei->{2}, '>>&', \*STDERR);
	open($lei->{3}, '<', '/');
	socketpair(my $x, my $y, AF_UNIX, SOCK_SEQPACKET, 0);
	$lei->{sock} = $x;
	require PublicInbox::LeiSelfSocket;
	PublicInbox::LeiSelfSocket->new($y); # adds to event loop
	$lei;
}

sub note_event ($@) { # runs lei_note_event for a given config file
	my ($cfg_f, @args) = @_;
	my $cfg = $PATH2CFG{$cfg_f} // return;
	eval { cfg2lei($cfg)->dispatch('note-event', @args) };
	carp "E: note-event $cfg_f: $@\n" if $@;
}

sub dir_idle_cb { # PublicInbox::DirIdle callback
	my ($ev, $sock_path) = @_; # $ev: Linux::Inotify2::Event or duck type
	my $fn = $ev->fullname;
	return if $fn eq ($$sock_path // ''); # just woke up for post_loop_do
	if ($fn =~ m!\A(.+)/(new|cur)/([^/]+)\z!) { # Maildir file
		my ($loc, $new_cur, $bn) = ("maildir:$1", $2, $3);
		$new_cur = '' if $ev->IN_DELETE || $ev->IN_MOVED_FROM;
		for my $cfg_f (keys %{$MDIR2CFGPATH->{$loc} // {}}) {
			note_event($cfg_f, $loc, $new_cur, $bn, $fn);
		}
	} elsif ($fn =~ m!\A(.+)/([0-9]+)\z!) { # MH mail message file
		my ($loc, $n, $new_cur) = ("mh:$1", $2, '+');
		$new_cur = '' if $ev->IN_DELETE || $ev->IN_MOVED_FROM;
		for my $cfg_f (keys %{$MDIR2CFGPATH->{$loc} // {}}) {
			note_event($cfg_f, $loc, $new_cur, $n, $fn);
		}
	} elsif ($fn =~ m!\A(.+)/\.mh_sequences\z!) { # reread flags
		my $loc = "mh:$1";
		for my $cfg_f (keys %{$MDIR2CFGPATH->{$loc} // {}}) {
			note_event($cfg_f, $loc, '.mh_sequences')
		}
	} # else we don't care
	if ($ev->can('cancel') && ($ev->IN_IGNORE || $ev->IN_UNMOUNT)) {
		$ev->cancel;
	}
	if ($fn =~ m!\A(.+)/(?:new|cur)\z! && !-e $fn) {
		delete $MDIR2CFGPATH->{"maildir:$1"};
	}
	if (!-e $fn) { # config file, Maildir, or MH dir gone
		delete $_->{$fn} for values %$MDIR2CFGPATH; # config file
		delete @$MDIR2CFGPATH{"maildir:$fn", "mh:$fn"};
		delete $PATH2CFG{$fn};
	}
}

sub can_stay_alive { # PublicInbox::DS::post_loop_do cb
	my ($sock_path, $dev_ino_expect) = @_;
	if (my @st = defined($$sock_path) ? stat($$sock_path) : ()) {
		if ($dev_ino_expect ne pack('dd', $st[0], $st[1])) {
			warn "$$sock_path dev/ino changed, quitting\n";
			$$sock_path = undef;
		}
	} elsif (defined($$sock_path)) { # ENOENT is common
		warn "stat($$sock_path): $!, quitting ...\n" if $! != ENOENT;
		undef $$sock_path;
		$quit->();
	}
	return 1 if defined($$sock_path);
	my $n = PublicInbox::DS::close_non_busy() or do {
		eval 'PublicInbox::LeiNoteEvent::flush_task()';
		# drop stores only if no clients
		for my $cfg (values %PATH2CFG) {
			my $lne = delete($cfg->{-lei_note_event});
			$lne->wq_close if $lne;
			my $sto = delete($cfg->{-lei_store}) // next;
			eval { $sto->wq_do('done') if $sto->{-wq_s1} };
			warn "E: $@ (dropping store for $cfg->{-f})" if $@;
			$sto->wq_close;
		}
	};
	# returns true: continue, false: stop
	$n + scalar(keys(%PublicInbox::DS::AWAIT_PIDS));
}

sub clear_tmp_xh { # awaitpid cb, called in lei-daemon
	my ($pid) = @_;
	my ($e, $s, @m) = ($? >> 8, $? & 127);
	push @m, " status=$e" if $e && $e != 66; # EX_NOINPUT ok
	push @m, " signal=$s" if $s;
	warn "W: xap_helper PID:$pid died: ", @m, "\n" if @m;
	undef $PublicInbox::Search::XHC;
}

sub spawn_tmp_xh { # called in top-level lei-daemon
	$PublicInbox::Search::XHC //= eval {
		my $xhc = PublicInbox::XapClient::start_helper(qw(-l -j0));
		awaitpid($xhc->{io}->attached_pid, \&clear_tmp_xh) if $xhc;
		$xhc;
	} || do {
		warn("E: $@ (will attempt to continue w/o Xapian helper)\n");
		undef;
	}
}

# lei(1) calls this when it can't connect
sub lazy_start {
	my ($sock_path, $errno, $narg) = @_;
	local ($errors_log, $listener, $PublicInbox::Search::XHC);

	# no point in using xap_helper w/o C++ features for local clients
	my $xh_cmd = eval { PublicInbox::XapHelperCxx::cmd() };
	$PublicInbox::Search::XHC = $xh_cmd ? undef : 0;
	if ($xh_cmd) {
		require PublicInbox::XapClient;
		require PublicInbox::XhcMset;
	}
	my ($sock_dir) = ($sock_path =~ m!\A(.+?)/[^/]+\z!);
	$errors_log = "$sock_dir/errors.log";
	my $addr = pack_sockaddr_un($sock_path);
	my $lk = PublicInbox::Lock->new($errors_log);
	umask(077) // die("umask(077): $!");
	$lk->lock_acquire;
	socket($listener, AF_UNIX, SOCK_SEQPACKET, 0);
	if ($errno == ECONNREFUSED || $errno == ENOENT) {
		return if connect($listener, $addr); # another process won
		unlink($sock_path) if $errno == ECONNREFUSED && -S $sock_path;
	} else {
		$! = $errno; # allow interpolation to stringify in die
		die "connect($sock_path): $!";
	}
	bind($listener, $addr);
	$lk->lock_release;
	undef $lk;
	my @st = stat($sock_path) or die "stat($sock_path): $!";
	my $dev_ino_expect = pack('dd', $st[0], $st[1]); # dev+ino
	local $oldset = PublicInbox::DS::block_signals(POSIX::SIGALRM);
	die "incompatible narg=$narg" if $narg != 5;
	$PublicInbox::IPC::send_cmd or die <<"";
Inline::C missing/unconfigured (narg=$narg);

	require PublicInbox::Listener;
	require PublicInbox::PktOp;
	(-p STDOUT) or die "E: stdout must be a pipe\n";
	open(STDIN, '+>>', $errors_log);
	STDIN->autoflush(1);
	dump_and_clear_log();
	POSIX::setsid() > 0 or die "setsid: $!";
	my $pid = PublicInbox::OnDestroy::fork_tmp;
	return if $pid;
	$0 = "lei-daemon $sock_path";
	local (%PATH2CFG, $MDIR2CFGPATH);
	local $daemon_pid = $$;
	$listener->blocking(0);
	listen $listener, 2**31 - 1; # kernel will clamp
	my $exit_code;
	my $pil = PublicInbox::Listener->new($listener, \&accept_dispatch);
	local $quit = do {
		my (undef, $eof_p) = PublicInbox::PktOp->pair;
		sub {
			$exit_code //= eval("POSIX::SIG$_[0] + 128") if @_;
			$dir_idle->close if $dir_idle; # EPOLL_CTL_DEL
			$dir_idle = undef; # let RC take care of it
			$PublicInbox::Search::XHC = undef; # ditto
			eval 'PublicInbox::LeiNoteEvent::flush_task()';
			my $lis = $pil or exit($exit_code // 0);
			# closing eof_p triggers \&noop wakeup
			$listener = $eof_p = $pil = $sock_path = undef;
			$lis->close; # DS::close
		};
	};
	my $sig = { CHLD => \&PublicInbox::DS::enqueue_reap };
	$sig->{$_} = $quit for qw(QUIT INT TERM);
	$sig->{$_} = \&PublicInbox::Config::noop for qw(HUP USR1 USR2);
	require PublicInbox::DirIdle;
	local $dir_idle = PublicInbox::DirIdle->new(\&dir_idle_cb, \$sock_path);
	$dir_idle->add_watches([$sock_dir]);
	local @PublicInbox::DS::post_loop_do = (\&can_stay_alive,
						\$sock_path, $dev_ino_expect);
	# STDIN was redirected to /dev/null above, closing STDERR and
	# STDOUT will cause the calling `lei' client process to finish
	# reading the <$daemon> pipe.
	local $SIG{__WARN__} = sub {
		$current_lei ? err($current_lei, @_) : warn(
		  strftime('%Y-%m-%dT%H:%M:%SZ', gmtime(time))," $$ ", @_);
	};
	local $SIG{PIPE} = 'IGNORE';
	local $SIG{ALRM} = 'IGNORE';
	open STDERR, '>&STDIN';
	open STDOUT, '>&STDIN';
	# $daemon pipe to `lei' closed, main loop begins:
	eval { PublicInbox::DS::event_loop($sig, $oldset) };
	warn "event loop error: $@\n" if $@;
	dump_and_clear_log();
	exit($exit_code // 0);
}

sub busy { 1 } # prevent daemon-shutdown if client is connected

# ensures stdout hits the FS before sock disconnects so a client
# can immediately reread it
sub DESTROY {
	my ($self) = @_;
	if (defined($self->{incr_pid}) && $self->{incr_pid} == $$) {
		for my $k (sort(grep(/\A-nr_/, keys %$self))) {
			my $nr = $self->{$k};
			substr($k, 0, length('-nr_'), '');
			$self->child_error(0, "$nr $k messages");
		}
	}
	$self->{1}->autoflush(1) if $self->{1};
	stop_pager($self);
	dump_and_clear_log();
	# preserve $? for ->fail or ->x_it code
}

sub wq_done_wait { # awaitpid cb (via wq_eof)
	my ($pid, $wq, $lei) = @_;
	local $current_lei = $lei;
	my $err_type = $lei->{-err_type};
	$? and $lei->child_error($?,
		$err_type ? "$err_type errors during $lei->{cmd} \$?=$?" : ());
	$lei->dclose;
}

sub fchdir {
	my ($lei) = @_;
	chdir($lei->{3} // die 'BUG: lei->{3} (CWD) gone');
}

sub wq_eof { # EOF callback for main daemon
	my ($lei, $wq_fld) = @_;
	local $current_lei = $lei;
	my $wq = delete $lei->{$wq_fld // 'wq1'};
	$lei->sto_barrier_request($wq);
	$wq // $lei->fail; # already failed
}

sub watch_state_ok ($) {
	my ($state) = $_[-1]; # $_[0] may be $self
	$state =~ /\Apause|(?:import|index|tag)-(?:ro|rw)\z/;
}

sub cancel_dir_watch ($$$) {
	my ($type, $d, $cfg_f) = @_;
	my $loc = "$type:".canonpath_harder($d);
	my $w = delete $MDIR2CFGPATH->{$loc}->{$cfg_f};
	delete $MDIR2CFGPATH->{$loc} if !(keys %{$MDIR2CFGPATH->{$loc}});
	$_->cancel for @$w;
}

sub add_dir_watch ($$$) {
	my ($type, $d, $cfg_f) = @_;
	$d = canonpath_harder($d);
	my $loc = "$type:$d";
	my @dirs = $type eq 'mh' ? ($d) : ("$d/cur", "$d/new");
	if (!exists($MDIR2CFGPATH->{$loc}->{$cfg_f})) {
		my @w = $dir_idle->add_watches(\@dirs, 1);
		push @{$MDIR2CFGPATH->{$loc}->{$cfg_f}}, @w if @w;
	}
}

sub refresh_watches {
	my ($lei) = @_;
	$dir_idle or return;
	my $cfg = _lei_cfg($lei) or return;
	my $old = $cfg->{-watches};
	my $watches = $cfg->{-watches} //= {};
	my %seen;
	my $cfg_f = $cfg->{'-f'};
	for my $w (grep(/\Awatch\..+\.state\z/, keys %$cfg)) {
		my $loc = substr($w, length('watch.'), -length('.state'));
		require PublicInbox::LeiWatch;
		$watches->{$loc} //= PublicInbox::LeiWatch->new($loc);
		$seen{$loc} = undef;
		my $state = $cfg->get_1("watch.$loc.state");
		if (!watch_state_ok($state)) {
			warn("watch.$loc.state=$state not supported\n");
		} elsif ($loc =~ /\A(maildir|mh):(.+)\z/i) {
			my ($type, $d) = ($1, $2);
			$state eq 'pause' ?
				cancel_dir_watch($type, $d, $cfg_f) :
				add_dir_watch($type, $d, $cfg_f);
		} else { # TODO: imap/nntp/jmap
			$lei->child_error(0, "E: watch $loc not supported, yet")
		}
	}

	# add all known Maildir folders as implicit watches
	my $lms = $lei->lms;
	if ($lms) {
		$lms->lms_write_prepare;
		for my $loc ($lms->folders(qr/\A(?:maildir|mh):/)) {
			my $old = $loc;
			my ($type, $d) = split /:/, $loc, 2;
			# fixup old bugs while we're iterating:
			$d = canonpath_harder($d);
			$loc = "$type:$d";
			$lms->rename_folder($old, $loc) if $old ne $loc;
			next if $watches->{$loc}; # may be set to pause
			require PublicInbox::LeiWatch;
			$watches->{$loc} = PublicInbox::LeiWatch->new($loc);
			$seen{$loc} = undef;
			add_dir_watch($type, $d, $cfg_f);
		}
	}
	if ($old) { # cull old non-existent entries
		for my $loc (keys %$old) {
			next if exists $seen{$loc};
			delete $old->{$loc};
			if ($loc =~ /\A(maildir|mh):(.+)\z/i) {
				cancel_dir_watch($1, $2, $cfg_f);
			} else { # TODO: imap/nntp/jmap
				$lei->child_error(0, "E: watch $loc TODO");
			}
		}
	}
	if (scalar keys %$watches) {
		$cfg->{-env} //= { %{$lei->{env}}, PWD => '/' }; # for cfg2lei
	} else {
		delete $cfg->{-watches};
	}
}

# TODO: support SHA-256
sub git_oid {
	my $eml = $_[-1];
	$eml->header_set($_) for @PublicInbox::Import::UNWANTED_HEADERS;
	git_sha(1, $eml);
}

sub lms {
	my ($lei, $creat) = @_;
	my $sto = $lei->{sto} // _lei_store($lei) // return;
	require PublicInbox::LeiMailSync;
	my $f = "$sto->{priv_eidx}->{topdir}/mail_sync.sqlite3";
	(-f $f || $creat) ? PublicInbox::LeiMailSync->new($f) : undef;
}

sub sto_barrier_request {
	my ($lei, $wq) = @_;
	return unless $lei->{sto} && $lei->{sto}->{-wq_s1};
	local $current_lei = $lei;
	if (my $n = $lei->{opt}->{'commit-delay'}) {
		eval { $lei->{sto}->wq_do('schedule_commit', $n) };
	} else {
		my $s = ($wq ? $wq->{lei_sock} : undef) // $lei->{sock};
		my $errfh = $lei->{2} // \*STDERR;
		my @io = $s ? ($errfh, $s) : ($errfh);
		eval { $lei->{sto}->wq_io_do('barrier', \@io, 1) };
	}
	warn($@) if $@;
}

sub cfg_dump ($$) {
	my ($lei, $f) = @_;
	my $ret = eval { PublicInbox::Config->git_config_dump($f, $lei) };
	return $ret if !$@;
	warn($@);
	undef;
}

sub request_umask { # assumes client is trusted and fast
	my ($lei) = @_;
	my $s = $lei->{sock} // return;
	send_eor($s, 'umask') // die "send: $!"; # never EAGAIN
	my ($v, $r, $u);
	do { # n.b. poll_in returns -1 on EINTR
		vec($v = '', fileno($s), 1) = 1;
		$r = poll_in $s, 60_000 or die 'timeout waiting for umask';
	} while ($r < 0 && $! == EINTR);
	do {
		$r = recv $s, $v, 5, 0;
		die "recv: $!" if !defined($r) && $! != EINTR;
	} while (!defined $r);
	($u, $lei->{client_umask}) = unpack('AV', $v);
	$u eq 'u' or warn "E: recv $v has no umask";
}

sub _stdin_cb { # PublicInbox::InputStream::consume callback for --stdin
	my (undef, $lei, $cb) = @_; # $_[-1] = $rbuf
	$_[1] // return $lei->fail("error reading stdin: $!");
	$lei->{stdin_buf} .= $_[-1];
	do_env($lei, $cb) if $_[-1] eq '';
}

sub slurp_stdin {
	my ($lei, $cb) = @_;
	require PublicInbox::InputStream;
	my $in = $lei->{0};
	if (-t $in) { # run cat via script/lei and read from it
		$in = undef;
		pipe($in, my $wr);
		say { $lei->{2} } '# enter query, Ctrl-D when done';
		send_exec_cmd($lei, [ $lei->{0}, $wr ], ['cat'], {});
	}
	PublicInbox::InputStream::consume($in, \&_stdin_cb, $lei, $cb);
}

1;
