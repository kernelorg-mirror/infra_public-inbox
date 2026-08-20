#!perl -w
# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# This talks to (XapHelperCxx.pm + xap_helper.h) or XapHelper.pm
# and will eventually allow users with neither XS nor SWIG Perl
# bindings to use Xapian as long as they have Xapian development
# headers/libs and a C++ compiler
package PublicInbox::XapClient;
use v5.12;
use PublicInbox::Spawn qw(spawn);
use Carp qw(croak);
use Socket qw(AF_UNIX SOCK_SEQPACKET);
use PublicInbox::IPC;
use autodie qw(pipe socketpair);
our $tries = -1; # set to zero by read-only daemon

sub mkreq {
	my ($self, $io, @arg) = @_;
	my $buf = join("\0", @arg, '');
	PublicInbox::IPC::sendcmd_eor($self->{io}, $io, $buf, $tries) //
		croak "sendcmd_eor: $!";
}

sub start_helper (@) {
	$PublicInbox::IPC::send_cmd or return; # can't work w/o SCM_RIGHTS
	my @argv = @_;
	socketpair(my $sock, my $in, AF_UNIX, SOCK_SEQPACKET, 0);
	my $cls = 'PublicInbox::XapHelperCxx';
	my $env;
	my $cmd = eval "require $cls; ${cls}::cmd()";
	if ($@) { # fall back to Perl + XS|SWIG
		return if "@argv" =~ /\b-l\b/; # no point w/o C++ in lei
		$cls = 'PublicInbox::XapHelper';
		# ensure the child process has the same @INC we do:
		$env = { PERL5LIB => join(':', @INC) };
		$cmd = [$^X, ($^W ? ('-w') : ()), "-M$cls", '-e',
			$cls.'::start(@ARGV)', '--' ];
	}
	push @$cmd, @argv;
	my $pid = spawn($cmd, $env, { 0 => $in });
	my $self = bless { io => $sock, impl => $cls }, __PACKAGE__;
	PublicInbox::IO::attach_pid($sock, $pid);
	$self;
}

1;
