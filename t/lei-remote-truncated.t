#!perl -w
# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>
# truncated responses from remote externals and inputs must not succeed
use v5.12; use PublicInbox::TestCommon;
use PublicInbox::IO qw(write_file);
require_mods(qw(lei -httpd psgi));
require_cmd 'curl';
my ($tmpdir, $for_destroy) = tmpdir;
my $psgi = "$tmpdir/trunc.psgi";
write_file '>', $psgi, <<'EOM';
use v5.12;
use IO::Compress::Gzip qw(gzip);
use PublicInbox::SHA qw(sha256_hex);
my $mbox = join('', map {
	my $i = $_;
	"From x\@y Thu Jan  1 00:00:00 1970\n".
	"From: x\@example.com\nMessage-ID: <$i\@example.com>\n".
	"Date: Thu, 01 Jan 1970 00:00:00 +0000\n\n".
	join('', map { sha256_hex("$i.$_")."\n" } 1..200)."\n";
} 1..30);
gzip(\$mbox => \(my $gz)) or die 'gzip';
my $half = substr($gz, 0, length($gz) / 2);
my @hdr = ('Content-Type', 'application/gzip');
sub DropBody::getline { shift(@{$_[0]}) // die "dropping connection\n" }
sub DropBody::close {}
sub {
	my ($env) = @_;
	if ($env->{PATH_INFO} =~ m!\A/ok/!) {
		[ 200, [ @hdr, 'Content-Length', length($gz) ], [ $gz ] ];
	} elsif ($env->{PATH_INFO} =~ m!\A/drop/!) { # curl exits 18
		[ 200, [ @hdr, 'Content-Length', length($gz) ],
			bless([ $half ], 'DropBody') ];
	} else { # valid HTTP, truncated gzip, curl exits 0
		[ 200, [ @hdr, 'Content-Length', length($half) ], [ $half ] ];
	}
}
EOM
my $sock = tcp_server;
my $cmd = [ '-httpd', '-W0', "--stdout=$tmpdir/1", "--stderr=$tmpdir/2",
	$psgi ];
my $td = start_script($cmd, undef, { 3 => $sock }) or xbail "-httpd: $?";
my $url = 'http://'.tcp_host_port($sock);

test_lei({ tmpdir => $tmpdir }, sub {
	my $nr_lastresult = sub {
		my $d = "$ENV{HOME}/.local/share/lei/saved-searches";
		my ($f) = glob("$d/$_[0]-*/lei.saved-search");
		my $cfg = PublicInbox::Config->new($f);
		scalar grep(/\.lastresult\z/, keys %$cfg);
	};
	lei_ok qw(q --save z:0.. -o), "$ENV{HOME}/ok", '--only', "$url/ok/";
	is($nr_lastresult->('ok'), 1, 'lastresult set on success');

	ok(!lei(qw(q --save z:0.. -o), "$ENV{HOME}/drop",
		'--only', "$url/drop/"), 'dropped connection fails');
	is($? >> 8, 18, 'curl exit code passed through');
	like($lei_err, qr/unexpected end of file/, 'gzip error shown');
	is($nr_lastresult->('drop'), 0, 'lastresult unset on failure');

	ok(!lei(qw(q z:0.. -o), "$ENV{HOME}/short", '--only', "$url/short/"),
		'truncated gzip fails w/ successful curl');
	like($lei_err, qr/unexpected end of file/, 'gzip error shown');

	ok(!lei('import', "$url/drop/t.mbox.gz"), 'import dropped fails');
	is($? >> 8, 18, 'curl exit code passed through on import');
	ok(!lei('import', "$url/short/t.mbox.gz"), 'import truncated fails');
	like($lei_err, qr/unexpected end of file/, 'gzip error on import');
});
done_testing;
