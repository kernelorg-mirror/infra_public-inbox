#!perl -w
# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>
use v5.12;
use PublicInbox::TestCommon;
use autodie;
use Socket qw(AF_UNIX SOCK_STREAM SOCK_SEQPACKET MSG_EOR);
use Fcntl qw(F_GETFL);
pipe(my $r, my $w);
my ($send, $recv);
require_ok 'PublicInbox::Spawn';
require POSIX;

my $do_test = sub { SKIP: {
	my ($type, $flag, $desc) = @_;
	my ($s1, $s2);
	my $src = 'a payload' x 40;
	socketpair($s1, $s2, AF_UNIX, $type, 0);
	my $io = [ $r, $w, $s1 ];
	$send->($s1, $io, $src, $flag);
	my @io = $recv->($s2, my $buf, length($src) * 2);
	is($buf, $src, 'got buffer payload '.$desc);
	my ($r1, $w1, $s1a);
	my $ck_io = sub {
		ok fcntl($io[$_], F_GETFL, 0), "open for fd[$_]" for (0..2);
		($r1, $w1, $s1a) = @io;
	};
	$ck_io->();
	my @exp = stat $r;
	my @cur = stat $r1;
	is("$exp[0]\0$exp[1]", "$cur[0]\0$cur[1]", '$r dev/ino matches');
	@exp = stat $w;
	@cur = stat $w1;
	is("$exp[0]\0$exp[1]", "$cur[0]\0$cur[1]", '$w dev/ino matches');
	@exp = stat $s1;
	@cur = stat $s1a;
	is("$exp[0]\0$exp[1]", "$cur[0]\0$cur[1]", '$s1 dev/ino matches');
	if ($type == SOCK_SEQPACKET) {
		$r1 = $w1 = $s1a = undef;
		$src = (',' x 1023) . '-' .('.' x 1024);
		$send->($s1, $io, $src, $flag);
		eval { @io = $recv->($s2, $buf, 1024) };
		like "$@", qr/recvmsg .* trunc/, "truncation noted $desc";
		is $buf, (',' x 1023) . '-', "truncated buf $desc";
		$ck_io->() if @io;
		if (my $leak_nr = $ENV{TEST_FD_LEAK_NR}) {
			my @p;
			pipe $p[0], $p[1];
			diag "TEST_FD_LEAK_NR=$leak_nr start ($desc): ".
				fileno($p[0]).', '.fileno($p[1]);
			my $n_exc;
			for (1..$leak_nr) {
				$send->($s1, $io, $src, $flag);
				eval { my @rio = $recv->($s2, $buf, 1024) };
				$n_exc += $@ ? 1 : 0;
			}
			is $n_exc, $leak_nr, 'got $leak_nr exceptions';
			pipe $p[2], $p[3];
			diag "TEST_FD_LEAK_NR=$leak_nr done ($desc): ".
				fileno($p[2]).', '.fileno($p[3]);
		}

		socketpair($s1, $s2, AF_UNIX, $type, 0);
		$r1 = $w1 = $s1a = undef;

		$s2->blocking(0);
		@io = $recv->($s2, $buf, length($src) + 1);
		ok($!{EAGAIN}, "EAGAIN set by ($desc)");
		is($buf, '', "recv buffer emptied on EAGAIN ($desc)");
		is_deeply(\@io, [ undef ], "EAGAIN $desc");
		$s2->blocking(1);

		if ('test ALRM') {
			my $alrm = 0;
			local $SIG{ALRM} = sub { $alrm++ };
			my $tgt = $$;
			my $pid = fork;
			if ($pid == 0) {
				# need to loop since Perl signals are racy
				# (the interpreter doesn't self-pipe)
				my $n = 3;
				while (tick(0.01 * $n) && --$n) {
					kill('ALRM', $tgt)
				}
				close $s1;
				POSIX::_exit(1);
			}
			close $s1;
			@io= $recv->($s2, $buf, length($src) + 1);
			waitpid($pid, 0);
			is_deeply(\@io, [], "EINTR->EOF $desc");
			ok($alrm, 'SIGALRM hit');
		}

		@io = $recv->($s2, $buf, length($src) + 1);
		is_deeply(\@io, [], "no FDs on EOF $desc");
		is($buf, '', "buffer cleared on EOF ($desc)");

		socketpair($s1, $s2, AF_UNIX, $type, 0);
		$s1->blocking(0);
		my $nsent = 0;
		my $srclen = length($src);
		while (defined(my $n = $send->($s1, $io, $src, $flag))) {
			$nsent += $n;
			fail "sent $n bytes of $srclen" if $n > $srclen;
		}
		ok($!{EAGAIN} || $!{ETOOMANYREFS} || $!{EMSGSIZE},
			"hit EAGAIN || ETOOMANYREFS || EMSGSIZE on send $desc")
			or diag "send failed with: $! (nsent=$nsent)";
		ok($nsent > 0, 'sent some bytes');
		undef $io;

		substr($src, 0, 1000, '') if $^O eq 'netbsd';

		socketpair($s1, $s2, AF_UNIX, $type, 0);
		is($send->($s1, [], $src, $flag), length($src), 'sent w/o IOs');
		$buf = 'nope';
		@io = $recv->($s2, $buf, length($src) * 2);
		is(scalar(@io), 0, 'no FDs received');
		is_xdeeply($buf, $src, 'recv w/o FDs');
	}
	socketpair($s1, $s2, AF_UNIX, $type, 0);
	is($send->($s1, undef, $src, $flag), length($src), 'sent w/ undef IO');
	@io = $recv->($s2, $buf = 'hi', length($src));
	is scalar(@io), 0, 'no FDs received';
	is $buf, $src, 'recv w/o FDs sent buffer';
} };

my $send_ic = PublicInbox::Spawn->can('send_cmd4');
my $recv_ic = PublicInbox::Spawn->can('recv_cmd4');
SKIP: {
	($send_ic && $recv_ic) or skip 'Inline::C not installed/enabled', 12;
	$send = $send_ic;
	$recv = $recv_ic;
	$do_test->(SOCK_STREAM, 0, 'Inline::C stream');
	$do_test->(SOCK_SEQPACKET, MSG_EOR, 'Inline::C seqpacket');
}

SKIP: {
	require_ok 'PublicInbox::Syscall';
	$send = PublicInbox::Syscall->can('send_cmd4') or
		skip "send_cmd4 not defined for $^O arch", 1;
	$recv = PublicInbox::Syscall->can('recv_cmd4') or
		skip "recv_cmd4 not defined for $^O arch", 1;
	$do_test->(SOCK_STREAM, 0, 'pure Perl stream');
	$do_test->(SOCK_SEQPACKET, MSG_EOR, 'pure Perl seqpacket');
}

done_testing;
