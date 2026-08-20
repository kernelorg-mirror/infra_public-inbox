#!perl -w
# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>
use v5.12;
use PublicInbox::TestCommon;
require_mods(qw(DBD::SQLite Xapian +SCM_RIGHTS)); # TODO: FIFO support?
use PublicInbox::Spawn qw(spawn);
use Socket qw(AF_UNIX SOCK_SEQPACKET SOCK_STREAM);
require PublicInbox::AutoReap;
use PublicInbox::IPC;
require PublicInbox::XapClient;
use PublicInbox::DS qw(now);
use autodie;
my ($tmp, $for_destroy) = tmpdir();

my $fi_data = './t/git.fast-import-data';
open my $fi_fh, '<', $fi_data;
open my $dh, '<', '.';
my $crepo = create_coderepo 'for-cindex', sub {
	my ($d) = @_;
	xsys_e([qw(git init -q --bare)]);
	xsys_e([qw(git fast-import --quiet)], undef, { 0 => $fi_fh });
	chdir($dh);
	run_script([qw(-cindex --dangerous -L medium --no-fsync -q -j1), '-g', $d])
		or xbail '-cindex internal';
	run_script([qw(-cindex --dangerous -L medium --no-fsync -q -j3 -d),
		"$d/cidx-ext", '-g', $d]) or xbail '-cindex "external"';
};
$dh = $fi_fh = undef;

my $v2 = create_inbox 'v2', indexlevel => 'medium', version => 2,
			tmpdir => "$tmp/v2", sub {
	my ($im) = @_;
	for my $f (qw(t/data/0001.patch t/data/binary.patch
			t/data/message_embed.eml
			t/solve/0001-simple-mod.patch
			t/solve/0002-rename-with-modifications.patch
			t/solve/bare.patch)) {
		$im->add(eml_load($f)) or BAIL_OUT;
	}
};

my $thr = create_inbox 'thr-ref+', indexlevel => 'medium', version => 2,
			tmpdir => "$tmp/thr", sub {
	my ($im) = @_;
	my $common = <<EOM;
From: <BOFH\@YHBT.net>
To: meta\@public-inbox.org
Date: Mon, 1 Apr 2019 08:15:21 +0000
EOM
	$im->add(PublicInbox::Eml->new(<<EOM));
${common}Subject: root message
Message-ID: <thread-root\@example>

hi
EOM
	my @t = qw(wildfires earthquake flood asteroid drought plague);
	my $nr = 0;
	for my $x (@t) {
		++$nr;
		$im->add(PublicInbox::Eml->new(<<EOM)) or xbail;
${common}Subject: Re: root reply
References: <thread-root\@example>
Message-ID: <thread-hit-$nr\@example>

$x
EOM
		$im->add(PublicInbox::Eml->new(<<EOM)) or xbail;
${common}Subject: broken thread from $x
References: <ghost-root\@example>
Message-ID: <thread-miss-$nr\@example>

$x
EOM
	}
};

my @ibx_idx = glob("$v2->{inboxdir}/xap*/?");
my @v2ol = ('-l', "$v2->{inboxdir}/open.lock");
my @ibx_shard_args = (@v2ol, map { ('-d', $_) } @ibx_idx);
my (@int) = glob("$crepo/public-inbox-cindex/cidx*/?");
my (@ext) = glob("$crepo/cidx-ext/cidx*/?");
is(scalar(@ext), 2, 'have 2 external shards') or diag explain(\@ext);
is(scalar(@int), 1, 'have 1 internal shard') or diag explain(\@int);
my @ciol = ('-l', "$crepo/public-inbox-cindex/open.lock");
my @cidx_int_shard_args = (@ciol, map { ('-d', $_) } @int);

my $doreq = sub {
	my ($s, @arg) = @_;
	my $err = ref($arg[-1]) ? pop(@arg) : \*STDERR;
	pipe(my $x, my $y);
	my $buf = join("\0", @arg, '');
	my @io = ($y, $err);
	PublicInbox::IPC::sendcmd_eor($s, \@io, $buf) //
		xbail "sendmsg: $!";
	$x;
};

local $SIG{PIPE} = 'IGNORE';
my $env = { PERL5LIB => join(':', @INC) };
my $test = sub {
	my (@cmd) = @_;
	socketpair(my $s, my $y, AF_UNIX, SOCK_SEQPACKET, 0);
	my $pid = spawn(\@cmd, $env, { 0 => $y });
	my $ar = PublicInbox::AutoReap->new($pid);
	diag "$cmd[-1] running pid=$pid";
	close $y;
	my $r = $doreq->($s, qw(test_inspect -d), $ibx_idx[0], @v2ol);
	my %info = map { split(/=/, $_, 2) } split(/ /, do { local $/; <$r> });
	is($info{has_threadid}, '1', 'has_threadid true for inbox');
	like($info{pid}, qr/\A\d+\z/, 'got PID from inbox inspect');

	$r = $doreq->($s, qw(test_inspect -d), $int[0], @ciol);
	my %cinfo = map { split(/=/, $_, 2) } split(/ /, do { local $/; <$r> });
	is($cinfo{has_threadid}, '0', 'has_threadid false for cindex');
	my $lei_mode = grep /\A-l\z/, @cmd;
	if ($lei_mode) {
		isnt $cinfo{pid}, $info{pid}, 'PID changed in lei mode';
	} else {
		is $cinfo{pid}, $info{pid}, 'PID unchanged for cindex';
	}

	my @dump = (qw(dump_ibx -A XDFID), @ibx_shard_args, qw(13 z:0..));
	$r = $doreq->($s, @dump);
	my @res;
	while (sysread($r, my $buf, 512) != 0) { push @res, $buf }
	is(grep(/\n\z/s, @res), scalar(@res), 'line buffered');

	pipe(my $err_rd, my $err_wr);
	$r = $doreq->($s, @dump, $err_wr);
	close $err_wr;
	my $res = do { local $/; <$r> };
	is(join('', @res), $res, 'got identical response w/ error pipe');
	my $stats = do { local $/; <$err_rd> };
	is($stats, "mset.size=6 nr_out=6\n", 'mset.size reported') or
		diag "res=$res";

	return wantarray ? ($ar, $s) : $ar if $cinfo{pid} == $pid || $lei_mode;

	# test worker management:
	kill('TERM', $cinfo{pid});
	my $tries = 0;
	do {
		$r = $doreq->($s, qw(test_inspect -d), $ibx_idx[0], @v2ol);
		%info = map { split(/=/, $_, 2) }
			split(/ /, do { local $/; <$r> });
	} while ($info{pid} == $cinfo{pid} && ++$tries < 10);
	isnt($info{pid}, $cinfo{pid}, 'spawned new worker');

	my %pids;
	$tries = 0;
	my @ins = ($s, qw(test_inspect -d), $ibx_idx[0], @v2ol);
	kill('TTIN', $pid);
	until (scalar(keys %pids) >= 2 || ++$tries > 100) {
		tick;
		my @r = map { $doreq->(@ins) } (0..100);
		for my $fh (@r) {
			my $buf = do { local $/; <$fh> } // die "read: $!";
			$buf =~ /\bpid=(\d+)/ and $pids{$1} = undef;
		}
	}
	is(scalar keys %pids, 2, 'have two pids') or
		diag 'pids='.explain(\%pids);

	kill('TTOU', $pid);
	%pids = ();
	my $delay = $tries * 0.11 * ($ENV{VALGRIND} ? 10 : 1);
	$tries = 0;
	diag 'waiting '.$delay.'s for SIGTTOU';
	tick($delay);
	until (scalar(keys %pids) == 1 || ++$tries > 100) {
		%pids = ();
		my @r = map { $doreq->(@ins) } (0..100);
		for my $fh (@r) {
			my $buf = do { local $/; <$fh> } // die "read: $!";
			$buf =~ /\bpid=(\d+)/ and $pids{$1} = undef;
		}
	}
	is(scalar keys %pids, 1, 'have one pid') or diag explain(\%pids);
	is($info{pid}, (keys %pids)[0], 'kept oldest PID after TTOU');

	wantarray ? ($ar, $s) : $ar;
};

my @NO_CXX = (1);
my $cxx_tested;
unless ($ENV{TEST_XH_CXX_ONLY}) {
	my $ar = $test->($^X, qw[-w -MPublicInbox::XapHelper -e
			PublicInbox::XapHelper::start('-j0')]);
	($ar, my $s) = $test->($^X, qw[-w -MPublicInbox::XapHelper -e
			PublicInbox::XapHelper::start('-j1')]);
}
SKIP: {
	my $cmd = eval {
		require PublicInbox::XapHelperCxx;
		PublicInbox::XapHelperCxx::cmd();
	};
	if ($@) {
		xbail "C++ build failed: $@" if $ENV{TEST_XH_CXX_ONLY};
		skip "XapHelperCxx build: $@", 1;
	} else {
		$cxx_tested = 1;
	}
	@NO_CXX = $ENV{TEST_XH_CXX_ONLY} ? (0) : (0, 1);
	my $ar = $test->(@$cmd, '-j0');
	$ar = $test->(@$cmd, '-j1');
	$ar = $test->(@$cmd, qw(-l));
};

require PublicInbox::CodeSearch;
my $cs_int = PublicInbox::CodeSearch->new("$crepo/public-inbox-cindex");
my $root2id_file = "$tmp/root2id";
my @id2root;
{
	open my $fh, '>', $root2id_file;
	my $i = -1;
	for ($cs_int->all_terms('G')) {
		print $fh $_, "\0", ++$i, "\0";
		$id2root[$i] = $_;
	}
	close $fh;
}

my $ar;
for my $n (@NO_CXX) {
	local $ENV{PI_NO_CXX} = $n;
	my $xhc = PublicInbox::XapClient::start_helper('-j0');
	pipe(my $err_r, my $err_w);

	# git patch-id --stable <t/data/0001.patch | awk '{print $1}'
	my $dfid = '91ee6b761fc7f47cad9f2b09b10489f313eb5b71';
	my $mid = '20180720072141.GA15957@example';

	pipe my $r, my $w;
	$xhc->mkreq([ $w, $err_w ], qw(dump_ibx -A XDFID -A Q),
				@ibx_shard_args, 9, "mid:$mid");
	close $err_w;
	close $w;
	my $res = do { local $/; <$r> };
	is($res, "$dfid 9\n$mid 9\n", "got expected result ($xhc->{impl})");
	my $err = do { local $/; <$err_r> };
	is($err, "mset.size=1 nr_out=2\n", "got expected status ($xhc->{impl})");

	pipe($err_r, $err_w);
	pipe $r, $w;
	$xhc->mkreq([ $w, $err_w ], qw(dump_roots -c -A XDFID),
			@cidx_int_shard_args,
			$root2id_file, 'dt:19700101'.'000000..');
	close $err_w;
	close $w;
	my @res = <$r>;
	is(scalar(@res), 5, 'got expected rows');
	is(scalar(@res), scalar(grep(/\A[0-9a-f]{40,} [0-9]+\n\z/, @res)),
		'entries match format');
	$err = do { local $/; <$err_r> };
	is $err, "mset.size=6 nr_out=5\n", "got expected status ($xhc->{impl})";

	# ensure we can try multiple queries and return the first one
	# with >0 matches
	for my $try ([[], []], [['thisbetternotmatchanything'], ['z:0..']],
			[['bogus...range ignored'], []],
			[['z:0.. dfn:Search.pm'], ['bogus...range never tried']]) {
		pipe $r, $w;
		diag explain($try);
		$xhc->mkreq([$w], qw(mset), @ibx_shard_args, @{$try->[0]},
					'dfn:lib/PublicInbox/Search.pm',
					@{$try->[1]});
		close $w;
		chomp((my $hdr, @res) = readline($r));
		like $hdr, qr/\bmset\.size=1\b/,
			"got expected header via mset ($xhc->{impl}";
		is scalar(@res), 1, 'got one result';
		@res = split /\0/, $res[0];
		{
			my $doc = $v2->search->xdb->get_document($res[0]);
			ok $doc, 'valid document retrieved';
			my @q = PublicInbox::Search::xap_terms('Q', $doc);
			is_deeply \@q, [ $mid ], 'docid usable';
		}
		ok $res[1] > 0 && $res[1] <= 100, 'pct > 0 && <= 100';
		is scalar(@res), 3, 'only 3 columns in result';
	}

	pipe $r, $w;
	$xhc->mkreq([$w], qw(mset), @ibx_shard_args,
				'dt:19700101'.'000000..');
	close $w;
	chomp((my $hdr, @res) = readline($r));
	like $hdr, qr/\bmset\.size=6\b/,
		"got expected header via multi-result mset ($xhc->{impl}";
	is(scalar(@res), 6, 'got 6 rows');
	for my $r (@res) {
		my ($docid, $pct, $rank, @rest) = split /\0/, $r;
		my $doc = $v2->search->xdb->get_document($docid);
		ok $pct > 0 && $pct <= 100,
			"pct > 0 && <= 100 #$docid ($xhc->{impl})";
		like $rank, qr/\A\d+\z/, 'rank is a digit';
		is scalar(@rest), 0, 'no extra rows returned';
	}

	pipe $r, $w;
	pipe $err_r, $err_w;
	$xhc->mkreq([$w, $err_w], qw(mset), @ibx_shard_args, 'bogus...range');
	close $w;
	close $err_w;
	chomp(@res = readline($r));
	is_deeply \@res, [], 'no output on bogus query';
	chomp(@res = readline($err_r));
	ok scalar(@res) && $res[0], 'got error on bogus query';

	my $nr;
	for my $i (7, 8, 39, 40) {
		pipe($err_r, $err_w);
		pipe($r, $w);
		$xhc->mkreq([ $w, $err_w ], qw(dump_roots -c -A),
				"XDFPOST$i", @cidx_int_shard_args,
				$root2id_file, 'dt:19700101'.'000000..');
		close $err_w;
		close $w;
		@res = <$r>;
		my @err = <$err_r>;
		if (defined $nr) {
			is scalar(@res), $nr,
				"got expected results ($xhc->{impl})";
		} else {
			$nr //= scalar @res;
			ok $nr, "got initial results ($xhc->{impl})";
		}
		my @oids = (join('', @res) =~ /^([a-f0-9]+) /gms);
		is_deeply [grep { length == $i } @oids], \@oids,
			"all OIDs match expected length ($xhc->{impl})";
		my ($nr_out) = ("@err" =~ /nr_out=(\d+)/);
		is $nr_out, scalar(@oids), "output count matches $xhc->{impl}"
			or diag explain(\@res, \@err);
	}
	pipe($err_r, $err_w);
	pipe $r, $w;
	$xhc->mkreq([ $w, $err_w ], qw(dump_ibx -A XDFPOST7),
			@ibx_shard_args, qw(13 rt:0..));
	close $err_w;
	close $w;
	@res = <$r>;
	my @err = <$err_r>;
	my ($nr_out) = ("@err" =~ /nr_out=(\d+)/);
	my @oids = (join('', @res) =~ /^([a-f0-9]{7}) /gms);
	is $nr_out, scalar(@oids), "output count matches $xhc->{impl}" or
		diag explain(\@res, \@err);

	if ($xhc->{impl} =~ /cxx/i) {
		require PublicInbox::XhcMset;
		my $over = $thr->over;
		my @thr_idx = glob("$thr->{inboxdir}/xap*/?");
		my @thr_shard_args = ('-l', "$thr->{inboxdir}/open.lock",
					map { ('-d', $_) } @thr_idx);

		my (@art, $mset, $err);
		my $capture = sub { ($mset, $err) = @_ };
		my $retrieve = sub {
			my ($qstr) = @_;
			pipe $r, $w;
			$xhc->mkreq([ $w ], 'mset', @thr_shard_args, $qstr);
			close $w;
			open my $err_rw, '+>', undef;
			PublicInbox::XhcMset->maybe_new($r, $err_rw,
							undef, $capture);
			map { $over->get_art($_->get_docid) } $mset->items;
		};
		@art = $retrieve->('thread:thread-root@example wildfires');
		is scalar(@art), 1, 'got 1 result';
		is scalar(grep { $_->{mid} =~ /thread-miss/ } @art), 0,
			'no thread misses in result';
		ok !$err, 'no error from thread:MSGID search';

		@art = $retrieve->('thread:thread-root@example');
		is scalar(@art), 7,
			'expected number of results for thread:MSGID';
		is scalar(grep {
				$_->{mid} eq 'thread-root@example' ||
				$_->{references} =~ /<thread-root\@example>/
			} @art),
			scalar(@art),
			'got all matching results for thread:MSGID';

		@art = $retrieve->('thread:"{ s:broken }"');
		is scalar(@art), 6,
			'expected number of results for thread:"{ SUBQUERY }"';
		is scalar(grep { $_->{subject} =~ /broken/ } @art),
			scalar(@art),
			'expected matches for thread:"{ SUBQUERY }"';

		@art = $retrieve->('thread:ghost-root@example');
		is scalar(@art), 6,
			'expected number of results for thread:GHOST-MSGID';
		is scalar(grep { $_->{references} =~ /ghost-root/ } @art),
			scalar(@art),
			'thread:MSGID works on ghosts';

		SKIP: {
			my $nr = $ENV{TEST_LEAK_NR} or
					skip 'TEST_LEAK_NR unset', 1;
			$ENV{VALGRIND} or diag
"W: `VALGRIND=' unset w/ TEST_LEAK_NR (using -fsanitize?)";
			for (1..$nr) {
				$retrieve->(
					'thread:thread-root@example wildfires');
				$retrieve->('thread:"{ s:broken }" wildfires');
			}
		}
	} elsif (!$cxx_tested) {
		diag 'thread: field processor requires C++';
	}
	SKIP: {
		skip 'TEST_XH_TIMEOUT unset', 1 if !$ENV{TEST_XH_TIMEOUT};
		diag 'testing timeouts...';
		for my $j (qw(0 1)) {
			my $t0 = now;
			pipe $r, $w;
			$xhc->mkreq([ $w ], qw(test_sleep -K 1 -d),
					$ibx_idx[0], @v2ol);
			close $w;
			is readline($r), undef, 'got EOF';
			my $diff = now - $t0;
			ok $diff < 3, "timeout didn't take too long -j$j";
			ok $diff >= 0.9, "timeout didn't fire prematurely -j$j";
			$xhc = PublicInbox::XapClient::start_helper('-j1');
		}
	}
}

SKIP: {
	my $nr = $ENV{TEST_XH_FDMAX} or
		skip 'TEST_XH_FDMAX unset', 1;
	my @xhc = map {
		local $ENV{PI_NO_CXX} = $_;
		PublicInbox::XapClient::start_helper('-j0');
	} @NO_CXX;
	my $n = 1;
	my $exp;
	for (0..(PublicInbox::Search::ulimit_n() * $nr)) {
		for my $xhc (@xhc) {
			pipe my $r, my $w;
			$xhc->mkreq([$w], qw(mset -Q), "tst$n=XTST$n",
					@ibx_shard_args, qw(rt:0..));
			close $w;
			chomp(my @res = readline($r));
			$exp //= $res[0];
			$exp eq $res[0] or
				is $exp, $res[0], "mset mismatch on n=$n";
			++$n;
		}
	}
	ok $exp, "got expected entries ($n)";
}

done_testing;
