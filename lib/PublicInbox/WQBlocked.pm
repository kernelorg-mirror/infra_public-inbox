# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# non-blocking workqueues, currently used by LeiNoteEvent to track renames
package PublicInbox::WQBlocked;
use v5.12;
use parent qw(PublicInbox::DS);
use PublicInbox::Syscall qw(EPOLLOUT EPOLLONESHOT);
use PublicInbox::IPC;
use Carp ();

sub new {
	my ($cls, $wq, $buf) = @_;
	my $self = bless { msgq => [$buf], }, $cls;
	$wq->{wqb} = $self->SUPER::new($wq->{-wq_s1}, EPOLLOUT|EPOLLONESHOT);
}

sub flush_send {
	my ($self) = @_;
	push(@{$self->{msgq}}, $_[1]) if defined($_[1]);
	while (defined(my $buf = shift @{$self->{msgq}})) {
		if (ref($buf) eq 'CODE') {
			$buf->($self); # could be \&PublicInbox::DS::close
		} elsif (defined(PublicInbox::IPC::sendcmd_eor(
					$self->{sock}, [], $buf))) {
			# success
		} else {
			if ($!{EAGAIN}) {
				PublicInbox::DS::epwait($self->{sock},
							EPOLLOUT|EPOLLONESHOT);
			} elsif ($!{ENOBUFS} || $!{ENOMEM}) {
				PublicInbox::DS::add_uniq_timer($self + 0,
						0.1, \&flush_send, $self);
			} else {
				Carp::croak("sendmsg: $!");
			}
			unshift @{$self->{msgq}}, $buf;
			last; # wait for ->event_step
		}
	}
}

sub enq_close { flush_send($_[0], $_[0]->can('close')) }

sub event_step { # called on EPOLLOUT wakeup
	my ($self) = @_;
	eval { flush_send($self) } if $self->{sock};
	if ($@) {
		warn $@;
		$self->close;
	}
}

1;
