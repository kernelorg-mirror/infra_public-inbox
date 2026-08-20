# Copyright all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# dummy placeholder socket for internal lei commands.
# This receives what script/lei receives, but isn't connected
# to an interactive terminal so I'm not sure what to do with it...
package PublicInbox::LeiSelfSocket;
use v5.12;
use parent qw(PublicInbox::DS);
use PublicInbox::Git qw(git_quote);
use PublicInbox::Syscall qw(EPOLLIN);
use PublicInbox::IPC;

sub new {
	my ($cls, $r) = @_;
	my $self = bless {}, $cls;
	$r->blocking(0);
	$self->SUPER::new($r, EPOLLIN);
}

sub event_step {
	my ($self) = @_;
	my ($buf, @io);
	@io = PublicInbox::IPC::recvcmd_eor($self->{sock}, $buf);
	if (scalar(@io) == 1 && !defined($io[0])) {
		return if $!{EAGAIN};
		die "recvmsg: $!" unless $!{ECONNRESET};
	}
	return $self->close if $buf eq '';
	warn 'W: unexpected self msg: ', git_quote($buf),
		' nfds=', scalar(@io), "\n";
	# TODO: figure out what to do with these messages...
}

1;
