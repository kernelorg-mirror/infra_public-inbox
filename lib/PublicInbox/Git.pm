# Copyright (C) all contributors <meta@public-inbox.org>
# License: GPLv2 or later <https://www.gnu.org/licenses/gpl-2.0.txt>
#
# Used to read files from a git repository without excessive forking.
# Used in our web interfaces as well as our -nntpd server.
# This is based on code in Git.pm which is GPLv2+, but modified to avoid
# dependence on environment variables for compatibility with mod_perl.
# There are also API changes to simplify our usage and data set.
package PublicInbox::Git;
use strict;
use v5.10.1; # TODO: check unicode_strings compat
use parent qw(Exporter PublicInbox::DS);
use PublicInbox::DS qw(now);
use autodie qw(socketpair sysread sysseek truncate);
use POSIX qw(SEEK_SET);
use Socket qw(AF_UNIX SOCK_STREAM);
use PublicInbox::Syscall qw(EPOLLIN EPOLLET);
use Errno qw(EAGAIN);
use File::Glob qw(bsd_glob GLOB_NOSORT);
use File::Spec ();
use PublicInbox::Spawn qw(spawn popen_rd run_qx which);
use PublicInbox::IO qw(read_all try_cat);
use PublicInbox::Tmpfile;
use Carp qw(croak carp);
use PublicInbox::SHA qw(sha_all);
our %HEXLEN2SHA = (40 => 1, 64 => 256);
our %OFMT2HEXLEN = (sha1 => 40, sha256 => 64);
our @EXPORT_OK = qw(git_unquote git_quote %HEXLEN2SHA %OFMT2HEXLEN
			$ck_unlinked_packs git_exe);
our $in_cleanup;
our $async_warn; # true in read-only daemons
our $noop = sub {};

# committerdate:unix is git 2.9.4+ (2017-05-05), so using raw instead
my @MODIFIED_DATE = qw[for-each-ref --sort=-committerdate
			--format=%(committerdate:raw) --count=1];

use constant {
	MAX_INFLIGHT => 18, # arbitrary, formerly based on PIPE_BUF
	BATCH_CMD_VER => v2.36.0, # git 2.36+
};

my %GIT_ESC = (
	a => "\a",
	b => "\b",
	f => "\f",
	n => "\n",
	r => "\r",
	t => "\t",
	v => "\013",
	'"' => '"',
	'\\' => '\\',
);
my %ESC_GIT = map { $GIT_ESC{$_} => $_ } keys %GIT_ESC;

my $EXE_ST = ''; # pack('JJ', st_dev, st_ino); # no `q' in some 32-bit builds
my ($GIT_EXE, $GIT_VER);

sub git_exe () {
	my $now = now;
	state $next_check = $now - 10;
	return $GIT_EXE if $now < $next_check;
	$next_check = $now + 10;
	$GIT_EXE = which('git') // die "git not found in $ENV{PATH}";
}

sub git_version () {
	my @st = stat(git_exe) or die "stat($GIT_EXE): $!";
	my $st = pack('JJ', $st[0], $st[1]);
	if ($st ne $EXE_ST) {
		my $v = run_qx([ $GIT_EXE, '--version' ]);
		die "$GIT_EXE --version: \$?=$?" if $?;
		$v =~ /\b([0-9]+(?:\.[0-9]+){2})/ or die
			"$GIT_EXE --version output: $v # unparseable";
		$GIT_VER = eval("v$1") // die "BUG: bad vstring: $1 ($v)";
		$EXE_ST = $st;
	}
	$GIT_VER;
}

# unquote pathnames used by git, see quote.c::unquote_c_style.c in git.git
sub git_unquote ($) {
	return $_[0] unless ($_[0] =~ /\A"(.*)"\z/);
	$_[0] = $1;
	$_[0] =~ s!\\([\\"abfnrtv]|[0-3][0-7]{2})!$GIT_ESC{$1}//chr(oct($1))!ge;
	$_[0];
}

sub git_quote ($) {
	if ($_[0] =~ s/([\\"\a\b\f\n\r\t\013]|[^[:print:]])/
		      '\\'.($ESC_GIT{$1}||sprintf("%03o",ord($1)))/egs) {
		return qq{"$_[0]"};
	}
	$_[0];
}

sub new {
	my ($class, $git_dir) = @_;
	$git_dir .= '/';
	$git_dir =~ tr!/!/!s;
	chop $git_dir;
	# may contain {-tmp} field for File::Temp::Dir
	my %dedupe = ($git_dir => undef);
	bless { git_dir => (keys %dedupe)[0] }, $class
}

sub git_path ($$) {
	my ($self, $path) = @_;
	$self->{-git_path}->{$path} //= do {
		my $d = $self->{git_dir};
		my $f = "$d/$path";
		if (-d "$d/objects") {
			$f;
		} else {
			local $/ = "\n";
			my $rdr = { 2 => \my $err };
			my $s = $self->qx([qw(rev-parse --git-path), $path],
					undef, $rdr);
			chomp $s;

			# git prior to 2.5.0 did not understand --git-path
			$s eq "--git-path\n$path" ? $f : $s;
		}
	};
}

sub alternates_changed {
	my ($self) = @_;
	my $alt = git_path($self, 'objects/info/alternates');
	use Time::HiRes qw(stat);
	my @st = stat($alt) or return 0;

	# can't rely on 'q' on some 32-bit builds, but `d' works
	my $st = pack('dd', $st[10], $st[7]); # 10: ctime, 7: size
	return 0 if ($self->{alt_st} // '') eq $st;
	$self->{alt_st} = $st; # always a true value
}

sub object_format {
	$_[0]->{object_format} //= do {
		my $fmt = $_[0]->qx(qw(config extensions.objectformat));
		$fmt eq "sha256\n" ? \'sha256' : \undef;
	}
}

sub last_check_err {
	my ($self) = @_;
	my $fh = $self->{err_c} or return '';
	my $size = -s $fh or return '';
	eval {
		sysseek $fh, 0, SEEK_SET;
		sysread($fh, my $buf, $size);
		truncate $fh, 0;
		$buf;
	} // $self->fail($@);
}

sub gcf_drain { # awaitpid cb
	my ($pid, $inflight, $bc) = @_;
	while (@$inflight) {
		my ($req, $cb, $arg) = splice(@$inflight, 0, 3);
		$req = $$req if ref($req);
		$bc and $req =~ s/\A(?:contents|info) //;
		$req =~ s/ .*//; # drop git_dir for Gcf2Client
		eval { $cb->(undef, $req, undef, undef, $arg) };
		warn "E: (in abort) $req: $@" if $@;
	}
}

sub _sock_cmd {
	my ($self, $batch, $err_c) = @_;
	$self->{sock} and Carp::confess('BUG: {sock} exists');
	socketpair(my $s1, my $s2, AF_UNIX, SOCK_STREAM, 0);
	$s1->blocking(0);
	my $opt = { pgid => 0, 0 => $s2, 1 => $s2 };
	my $gd = $self->{git_dir};
	if ($gd =~ s!/([^/]+/[^/]+)\z!/!) {
		$opt->{-C} = $gd;
		$gd = $1;
	}

	# git 2.31.0+ supports -c core.abbrev=no, don't bother with
	# core.abbrev=64 since not many releases had SHA-256 prior to 2.31
	my $abbr = git_version lt v2.31.0 ? 40 : 'no';
	my @cmd = ($GIT_EXE, "--git-dir=$gd", '-c', "core.abbrev=$abbr",
			'cat-file', "--$batch");
	if ($err_c) {
		my $id = "git.$self->{git_dir}.$batch.err";
		$self->{err_c} = $opt->{2} = tmpfile($id, undef, 1) or
						$self->fail("tmpfile($id): $!");
	}
	my $inflight = []; # TODO consider moving this into the IO object
	my $pid = spawn(\@cmd, undef, $opt);
	$self->{sock} = PublicInbox::IO::attach_pid($s1, $pid,
				\&gcf_drain, $inflight, $self->{-bc});
	$self->{inflight} = $inflight;
}

sub cat_async_retry ($$) {
	my ($self, $old_inflight) = @_;

	# {inflight} may be non-existent, but if it isn't we delete it
	# here to prevent cleanup() from waiting:
	my ($sock, $epwatch) = delete @$self{qw(sock epwatch inflight)};
	$self->SUPER::close if $epwatch;
	my $new_inflight = batch_prepare($self);

	while (my ($oid, $cb, $arg) = splice(@$old_inflight, 0, 3)) {
		write_all($self, $oid."\n", \&cat_async_step, $new_inflight);
		$oid = \$oid if !@$new_inflight; # to indicate oid retried
		push @$new_inflight, $oid, $cb, $arg;
	}
	undef $sock; # gcf_drain may run from PublicInbox::IO::DESTROY
	cat_async_step($self, $new_inflight); # take one step
}

sub gcf_inflight ($) {
	my ($self) = @_;
	# FIXME: the first {sock} check can succeed but Perl can complain
	# about an undefined value.  Not sure why or how this happens but
	# t/imapd.t can complain about it, sometimes.
	if ($self->{sock}) {
		if (eval { $self->{sock}->can_reap }) {
			return $self->{inflight};
		} elsif ($@) {
			no warnings 'uninitialized';
			warn "E: $self sock=$self->{sock}: can_reap failed: ".
				"$@ (continuing...)";
		}
		delete @$self{qw(sock inflight)};
	} else {
		$self->close;
	}
	undef;
}

# returns true if prefetch is successful
sub async_prefetch {
	my ($self, $oid, $cb, $arg) = @_;
	my $inflight = gcf_inflight($self) or return;
	return if @$inflight;
	substr($oid, 0, 0) = 'contents ' if $self->{-bc};
	write_all($self, "$oid\n", \&cat_async_step, $inflight);
	push(@$inflight, $oid, $cb, $arg);
}

sub cat_async_step ($$) {
	my ($self, $inflight) = @_;
	croak 'BUG: inflight empty or odd' if scalar(@$inflight) < 3;
	my ($req, $cb, $arg) = @$inflight[0, 1, 2];
	my ($bref, $oid, $type, $size);
	my $head = $self->{sock}->my_gets;
	my $cmd = ref($req) ? $$req : $req;
	# ->fail may be called via Gcf2Client.pm
	my $info = $self->{-bc} && substr($cmd, 0, 5) eq 'info ';
	if (!defined $head) {
		$self->fail("E: $self->{git_dir} gone? (\$!=$!)");
	} elsif ($head =~ /^([0-9a-f]{40,}) (\S+) ([0-9]+)$/) {
		($oid, $type, $size) = ($1, $2, $3 + 0);
		unless ($info) { # --batch-command
			$bref = $self->{sock}->my_bufread($size + 1) or
				$self->fail(defined($bref) ?
						'read EOF' : "read: $!");
			chop($$bref) eq "\n" or
					$self->fail('LF missing after blob');
		}
	} elsif ($info && $head =~ / (missing|ambiguous)\n/) {
		$type = $1;
		$oid = substr($cmd, 5); # remove 'info '
	} elsif ($head =~ s/ missing\n//s) {
		$oid = $head;
		# ref($req) indicates it's already been retried
		# -gcf2 retries internally, so it never hits this path:
		if (!ref($req) && !$in_cleanup && $self->alternates_changed) {
			return cat_async_retry($self, $inflight);
		}
		$type = 'missing';
		if ($oid eq '') {
			$oid = $cmd;
			$oid =~ s/\A(?:contents|info) // if $self->{-bc};
		}
	} else {
		my $err = $! ? " ($!)" : '';
		$self->fail("bad result from async cat-file: $head$err");
	}
	splice(@$inflight, 0, 3); # don't retry $cb on ->fail
	eval { $cb->($bref, $oid, $type, $size, $arg) };
	async_err($self, $req, $oid, $@, $info ? 'check' : 'cat') if $@;
}

sub cat_async_wait ($) {
	my ($self) = @_;
	my $inflight = gcf_inflight($self) or return;
	cat_async_step($self, $inflight) while (scalar(@$inflight));
}

sub batch_prepare ($) {
	my ($self) = @_;
	if (git_version ge BATCH_CMD_VER) {
		$self->{-bc} = 1;
		_sock_cmd($self, 'batch-command', 1);
	} else {
		_sock_cmd($self, 'batch');
	}
}

sub _cat_file_cb {
	my ($bref, $oid, $type, $size, $result) = @_;
	@$result = ($bref, $oid, $type, $size);
}

sub cat_file {
	my ($self, $oid) = @_;
	my $result = [];
	cat_async($self, $oid, \&_cat_file_cb, $result);
	cat_async_wait($self);
	wantarray ? @$result : $result->[0];
}

sub check_async_step ($$) {
	my ($ck, $inflight) = @_;
	croak 'BUG: inflight empty or odd' if scalar(@$inflight) < 3;
	my ($req, $cb, $arg) = @$inflight[0, 1, 2];
	chomp(my $line = $ck->{sock}->my_gets);
	my ($hex, $type, $size) = split(/ /, $line);

	# git <2.21 would show `dangling' (2.21+ shows `ambiguous')
	# https://public-inbox.org/git/20190118033845.s2vlrb3wd3m2jfzu@dcvr/T/
	if ($hex eq 'dangling') {
		my $ret = $ck->{sock}->my_bufread($type + 1);
		$ck->fail(defined($ret) ? 'read EOF' : "read: $!") if !$ret;
	}
	splice(@$inflight, 0, 3); # don't retry $cb on ->fail
	eval { $cb->(undef, $hex, $type, $size, $arg) };
	async_err($ck, $req, $hex, $@, 'check') if $@;
}

sub check_async_wait ($) {
	my ($self) = @_;
	return cat_async_wait($self) if $self->{-bc};
	my $ck = $self->{ck} or return;
	my $inflight = gcf_inflight($ck) or return;
	check_async_step($ck, $inflight) while (scalar(@$inflight));
}

# git <2.36
sub ck {
	$_[0]->{ck} //= bless { git_dir => $_[0]->{git_dir} },
				'PublicInbox::GitCheck';
}

sub check_async_begin ($) {
	my ($self) = @_;
	cleanup($self) if alternates_changed($self);
	if (git_version ge BATCH_CMD_VER) {
		$self->{-bc} = 1;
		_sock_cmd($self, 'batch-command', 1);
	} else {
		_sock_cmd($self = ck($self), 'batch-check', 1);
	}
}

sub write_all {
	my ($self, $buf, $read_step, $inflight) = @_;
	$self->{sock} // Carp::confess 'BUG: no {sock}';
	Carp::confess('BUG: not an array') if ref($inflight) ne 'ARRAY';
	$read_step->($self, $inflight) while @$inflight >= MAX_INFLIGHT;
	do {
		my $w = syswrite($self->{sock}, $buf);
		if (defined $w) {
			return if $w == length($buf);
			substr($buf, 0, $w, ''); # sv_chop
		} elsif ($! != EAGAIN) {
			$self->fail("write: $!");
		}
		$read_step->($self, $inflight);
	} while (1);
}

sub check_async ($$$$) {
	my ($self, $oid, $cb, $arg) = @_;
	my $inflight;
	if ($self->{-bc}) { # likely as time goes on
batch_command:
		$inflight = gcf_inflight($self) // cat_async_begin($self);
		substr($oid, 0, 0) = 'info ';
		write_all($self, "$oid\n", \&cat_async_step, $inflight);
	} else { # accounts for git upgrades while we're running:
		my $ck = $self->{ck}; # undef OK, maybe set in check_async_begin
		$inflight = ($ck ? gcf_inflight($ck) : undef)
				 // check_async_begin($self);
		goto batch_command if $self->{-bc};
		write_all($self->{ck}, "$oid\n", \&check_async_step, $inflight);
	}
	push(@$inflight, $oid, $cb, $arg);
}

sub _check_cb { # check_async callback
	my (undef, $hex, $type, $size, $result) = @_;
	@$result = ($hex, $type, $size);
}

sub check {
	my ($self, $oid) = @_;
	my $result = [];
	check_async($self, $oid, \&_check_cb, $result);
	check_async_wait($self);
	my ($hex, $type, $size) = @$result;

	# git <2.21 would show `dangling' (2.21+ shows `ambiguous')
	# https://public-inbox.org/git/20190118033845.s2vlrb3wd3m2jfzu@dcvr/T/
	return if $type =~ /\A(?:missing|ambiguous)\z/ || $hex eq 'dangling';
	($hex, $type, $size);
}

sub fail {
	my ($self, $msg) = @_;
	$self->close;
	croak(ref($self) . ' ' . ($self->{git_dir} // '') . ": $msg");
}

sub async_err ($$$$$) {
	my ($self, $req, $oid, $err, $action) = @_;
	$req = $$req if ref($req); # retried
	my $msg = "E: $action $req ($oid): $err";
	$async_warn ? carp($msg) : $self->fail($msg);
}

sub cmd {
	my $self = shift;
	[ git_exe(), "--git-dir=$self->{git_dir}", @_ ]
}

# $git->popen(qw(show f00)); # or
# $git->popen(qw(show f00), { GIT_CONFIG => ... }, { 2 => ... });
sub popen {
	my ($self, $cmd) = splice(@_, 0, 2);
	$cmd = $self->cmd(ref($cmd) ? @$cmd :
			($cmd, grep { defined && !ref } @_));
	popen_rd($cmd, grep { !defined || ref } @_); # env and opt
}

# same args as popen above
sub qx {
	my $fh = popen(@_);
	if (wantarray) {
		my @ret = <$fh>;
		$fh->close; # caller should check $?
		@ret;
	} else {
		local $/;
		my $ret = <$fh>;
		$fh->close; # caller should check $?
		$ret;
	}
}

sub date_parse {
	my $self = shift;
	map {
		substr($_, length('--max-age='), -1)
	} $self->qx('rev-parse', map { "--since=$_" } @_);
}

sub cat_active ($) {
	scalar(@{gcf_inflight($_[0]) // []}) ||
		($_[0]->{ck} && scalar(@{gcf_inflight($_[0]->{ck}) // []}))
}

# n.b.: use async_barrier for new code
# check_async and cat_async may trigger the other, so ensure they're
# both completely done by using this:
sub async_wait_all ($) {
	my ($self) = @_;
	while (cat_active($self)) {
		check_async_wait($self);
		cat_async_wait($self);
	}
}

# runs $on_destroy (PublicInbox::OnDestroy) after all currently in-flight
# requests are done:
sub async_barrier {
	my ($self, $on_destroy) = @_;
	if (my $ck = $self->{ck}) { # old git only
		if (my $inflight = gcf_inflight($ck)) {
			write_all $ck, "\n", \&check_async_step, $inflight;
			push @$inflight, '', $noop, $on_destroy;
		}
	}
	if (my $inflight = gcf_inflight($self)) {
		my $req = $self->{-bc} ? \'contents ' : \'';
		write_all $self, "$$req\n", \&cat_async_step, $inflight;
		push @$inflight, $req, $noop, $on_destroy;
	}
}

# returns true if there are pending "git cat-file" processes
sub cleanup {
	my ($self, $lazy) = @_;
	($lazy && cat_active($self)) and
		return $self->{epwatch} ? watch_async($self) : 1;
	local $in_cleanup = 1;
	async_wait_all($self);
	$_->close for ($self, (delete($self->{ck}) // ()));
	undef;
}

# assuming a well-maintained repo, this should be a somewhat
# accurate estimation of its size
# TODO: show this in the WWW UI as a hint to potential cloners
sub packed_bytes {
	my ($self) = @_;
	my $n = 0;
	my $pack_dir = git_path($self, 'objects/pack');
	$n += (-s $_ // 0) for (bsd_glob("$pack_dir/*.pack", GLOB_NOSORT));
	$n
}

sub DESTROY { cleanup($_[0]) }

sub local_nick ($) {
	# don't show full FS path, basename should be OK:
	$_[0]->{nick} // ($_[0]->{git_dir} =~ m!/([^/]+?)(?:/*\.git/*)?\z! ?
			"$1.git" : undef);
}

sub host_prefix_url ($$) {
	my ($env, $url) = @_;
	return $url if index($url, '//') >= 0;
	require PublicInbox::Hval;
	PublicInbox::Hval::psgi_base_url($env) . '/' . $url;
}

sub base_url { # for coderepos, PSGI-only
	my ($self, $env) = @_; # env - PSGI env
	my $nick = $self->{nick} // return undef;
	my $url = host_prefix_url($env, '');
	# for mount in Plack::Builder
	$url .= '/' if substr($url, -1, 1) ne '/';
	$url . $nick . '/';
}

sub isrch {} # TODO

sub pub_urls {
	my ($self, $env) = @_;
	if (my $urls = $self->{cgit_url}) {
		map { host_prefix_url($env, $_) } @$urls;
	} else {
		(base_url($self, $env) // '???');
	}
}

sub cat_async_begin {
	my ($self) = @_;
	cleanup($self) if $self->alternates_changed;
	die 'BUG: already in async' if gcf_inflight($self);
	batch_prepare($self);
}

sub cat_async ($$$;$) {
	my ($self, $oid, $cb, $arg) = @_;
	my $inflight = gcf_inflight($self) // cat_async_begin($self);
	substr($oid, 0, 0) = 'contents ' if $self->{-bc};
	write_all($self, $oid."\n", \&cat_async_step, $inflight);
	push(@$inflight, $oid, $cb, $arg);
}

# returns the modified time of a git repo, same as the "modified" field
# of a grokmirror manifest
sub modified ($;$) {
	my $fh = $_[1] // popen($_[0], @MODIFIED_DATE);
	(split(/ /, <$fh> // time))[0] + 0; # integerize for JSON
}

sub cat_desc ($) {
	my $desc = try_cat($_[0]);
	chomp $desc;
	utf8::decode($desc);
	$desc =~ s/\s+/ /smg;
	$desc eq '' ? undef : $desc;
}

sub description {
	cat_desc("$_[0]->{git_dir}/description") // 'Unnamed repository';
}

sub cloneurl {
	my ($self, $env) = @_;
	$self->{cloneurl} // do {
		my @urls = split(/\s+/s, try_cat("$self->{git_dir}/cloneurl"));
		scalar(@urls) ? ($self->{cloneurl} = \@urls) : undef;
	} // [ substr(base_url($self, $env), 0, -1) ];
}

# for grokmirror, which doesn't read gitweb.description
# templates/hooks--update.sample and git-multimail in git.git
# only match "Unnamed repository", not the full contents of
# templates/this--description in git.git
sub manifest_entry {
	my ($self, $epoch, $default_desc) = @_;
	my $gd = $self->{git_dir};
	my @git = (git_exe, "--git-dir=$gd");
	my $sr = popen_rd([@git, 'show-ref']);
	my $own = popen_rd([@git, qw(config gitweb.owner)]);
	my $mod = popen_rd([@git, @MODIFIED_DATE]);
	my $buf = description($self);
	if (defined $epoch && index($buf, 'Unnamed repository') == 0) {
		$buf = "$default_desc [epoch $epoch]";
	}
	my $ent = { description => $buf, reference => undef };
	if (open(my $alt, '<', "$gd/objects/info/alternates")) {
		# n.b.: GitPython doesn't seem to handle comments or C-quoted
		# strings like native git does; and we don't for now, either.
		local $/ = "\n";
		chomp(my @alt = <$alt>);

		# grokmirror only supports 1 alternate for "reference",
		if (scalar(@alt) == 1) {
			$buf = File::Spec->rel2abs($alt[0], "$gd/objects");
			$buf =~ s!/[^/]+/?\z!!; # basename
			$ent->{reference} = $buf;
		}
	}
	$ent->{fingerprint} = sha_all(1, $sr)->hexdigest;
	$sr->close or return; # empty, uninitialized git repo
	$ent->{modified} = modified(undef, $mod);
	chomp($buf = <$own> // '');
	utf8::decode($buf);
	$ent->{owner} = $buf eq '' ? undef : $buf;
	$ent;
}

our $ck_unlinked_packs = $^O eq 'linux' ? sub {
	# FIXME: port gcf2-like over to git.git so we won't need to
	# deal with libgit2
	my $s = try_cat "/proc/$_[0]/maps";
	$s =~ /\.(?:idx|pack) \(deleted\)/s ? 1 : undef;
} : undef;

# returns true if there are pending cat-file processes
sub cleanup_if_unlinked {
	my ($self) = @_;
	$ck_unlinked_packs or return cleanup($self, 1);
	# Linux-specific /proc/$PID/maps access
	# TODO: support this inside git.git
	my $nr_live = 0;
	for my $obj ($self, ($self->{ck} // ())) {
		my $sock = $obj->{sock} // next;
		my $pid = $sock->attached_pid // next;
		$ck_unlinked_packs->($pid) and return cleanup($self, 1);
		++$nr_live;
	}
	$nr_live;
}

sub event_step {
	my ($self) = @_;
	my $inflight = gcf_inflight($self);
	if ($inflight && @$inflight) {
		eval { $self->cat_async_step($inflight) };
		warn "E: $self->{git_dir}: $@" if $@;
		return $self->close unless $self->{sock};
		# don't loop here to keep things fair, but we must requeue
		# if there's already-read data in pi_io_rbuf
		$self->requeue if $self->{sock}->has_rbuf;
	}
}

sub schedule_cleanup {
	my ($self) = @_;
	PublicInbox::DS::add_uniq_timer($self+0, 30, \&cleanup, $self, 1);
}

# idempotently registers with DS epoll/kqueue/select/poll
sub watch_async ($) {
	my ($self) = @_;
	schedule_cleanup($self);
	$self->{sock} // return;
	$self->{epwatch} //= do {
		$self->SUPER::new($self->{sock}, EPOLLIN);
		\undef;
	}
}

sub close {
	my ($self) = @_;
	delete @$self{qw(-bc err_c inflight -prev_oids)};
	delete($self->{epwatch}) ? $self->SUPER::close : delete($self->{sock});
	# gcf_drain may run from PublicInbox::IO::DESTROY
}

package PublicInbox::GitCheck; # only for git <2.36
use v5.10.1; # TODO: change PublicInbox::Git to v5.12
our @ISA = qw(PublicInbox::Git);
no warnings 'once';

# for event_step
*cat_async_step = \&PublicInbox::Git::check_async_step;

1;
__END__
=pod

=head1 NAME

PublicInbox::Git - git wrapper

=head1 VERSION

version 1.0

=head1 SYNOPSIS

	use PublicInbox::Git;
	chomp(my $git_dir = `git rev-parse --git-dir`);
	$git_dir or die "GIT_DIR= must be specified\n";
	my $git = PublicInbox::Git->new($git_dir);

=head1 DESCRIPTION

Unstable API outside of the L</new> method.
It requires L<git(1)> to be installed.

=head1 METHODS

=cut

=head2 new

	my $git = PublicInbox::Git->new($git_dir);

Initialize a new PublicInbox::Git object for use with L<PublicInbox::Import>
This is the only public API method we support.  Everything else
in this module is subject to change.

=head1 SEE ALSO

L<Git>, L<PublicInbox::Import>

=head1 CONTACT

All feedback welcome via plain-text mail to L<mailto:meta@public-inbox.org>

The mail archives are hosted at L<https://public-inbox.org/meta/>

=head1 COPYRIGHT

Copyright (C) 2016 all contributors L<mailto:meta@public-inbox.org>

License: AGPL-3.0+ L<http://www.gnu.org/licenses/agpl-3.0.txt>

=cut
