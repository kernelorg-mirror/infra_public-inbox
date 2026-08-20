# This is a fork of the (for now) unmaintained Sys::Syscall 0.25,
# specifically the Debian libsys-syscall-perl 0.25-6 version to
# fix upstream regressions in 0.25.
#
# See devel/sysdefs-list in the public-inbox source tree for maintenance
# <https://80x24.org/public-inbox.git>, and machines from the GCC Farm:
# <https://portal.cfarm.net/>
#
# This license differs from the rest of public-inbox
#
# This module is Copyright (c) 2005 Six Apart, Ltd.
# Copyright (C) all contributors <meta@public-inbox.org>
#
# All rights reserved.
#
# You may distribute under the terms of either the GNU General Public
# License or the Artistic License, as specified in the Perl README file.
package PublicInbox::Syscall;
use v5.12;
use parent qw(Exporter);
use bytes qw(length substr);
use Carp qw(croak);
use POSIX qw(ENOENT ENOSYS EINVAL O_NONBLOCK);
use Socket qw(SOL_SOCKET SCM_RIGHTS MSG_CTRUNC MSG_TRUNC);
use Config;
our %SIGNUM = (WINCH => 28); # most Linux, {Free,Net,Open}BSD, *Darwin
our ($INOTIFY, %CONST);
my $FSWORD_T = 'l!'; # for unpack, tested on x86 and x86-64, `q' on x32
use List::Util qw(sum);
use Errno qw(EINTR);

# $VERSION = '0.25'; # Sys::Syscall version
our @EXPORT_OK = qw(epoll_create
		EPOLLIN EPOLLOUT EPOLLET
		EPOLL_CTL_ADD EPOLL_CTL_DEL EPOLL_CTL_MOD
		EPOLLONESHOT EPOLLEXCLUSIVE
		rename_noreplace %SIGNUM $F_SETPIPE_SZ defrag_file
		MY_SEQPACKET_MAX);
use constant {
	EPOLLIN => 1,
	EPOLLOUT => 4,
	# EPOLLERR => 8,
	# EPOLLHUP => 16,
	# EPOLLRDBAND => 128,
	EPOLLEXCLUSIVE => (1 << 28),
	EPOLLONESHOT => (1 << 30),
	EPOLLET => (1 << 31),
	EPOLL_CTL_ADD => 1,
	EPOLL_CTL_DEL => 2,
	EPOLL_CTL_MOD => 3,
	SIZEOF_int => $Config{intsize},
	SIZEOF_size_t => $Config{sizesize},
	SIZEOF_ptr => $Config{ptrsize},
	NUL => "\0",
};

use constant TMPL_size_t => SIZEOF_size_t == 8 ? 'Q' : 'L';

our ($SYS_epoll_create,
	$SYS_epoll_ctl,
	$SYS_epoll_pwait,
	$SYS_renameat2,
	$F_SETPIPE_SZ,
	$SYS_sendmsg,
	$SYS_recvmsg);

my $SYS_fstatfs; # don't need fstatfs64, just statfs.f_type
my ($FS_IOC_GETFLAGS, $FS_IOC_SETFLAGS, $SYS_writev,
	$BTRFS_IOC_DEFRAG);
our ($machine, $kver);
my $SFD_CLOEXEC = 02000000; # Perl does not expose O_CLOEXEC
our $no_deprecated = 0;
BEGIN {
	(undef, undef, my $release, undef, $machine) = POSIX::uname();
	($kver) = ($release =~ /([0-9]+(?:\.(?:[0-9]+))+)/);
	$kver = eval("v$kver") // die "bad release=$release from uname";
}

if ($^O eq "linux") {
	$F_SETPIPE_SZ = 1031;
	$SYS_renameat2 = 0 if $kver lt v3.15;
	$SYS_epoll_pwait = 0 if $kver lt v2.6.19;
	# whether the machine requires 64-bit numbers to be on 8-byte
	# boundaries.
	my $u64_mod_8 = 0;

	if (SIZEOF_ptr == 4) {
		# if we're running on an x86_64 kernel, but a 32-bit process,
		# we need to use the x32 or i386 syscall numbers.
		if ($machine eq 'x86_64') {
			my $s = $Config{cppsymbols};
			$machine = ($s =~ /\b__ILP32__=1\b/ &&
					$s =~ /\b__x86_64__=1\b/) ?
				'x32' : 'i386'
		} elsif ($machine eq 'mips64') { # similarly for mips64 vs mips
			$machine = 'mips';
		}
	}
	if ($machine =~ m/^i[3456]86$/) {
		$SYS_epoll_create = 254;
		$SYS_epoll_ctl = 255;
		$SYS_epoll_pwait //= 319;
		$SYS_renameat2 //= 353;
		$SYS_fstatfs = 100;
		$SYS_sendmsg = 370;
		$SYS_recvmsg = 372;
		$SYS_writev = 146;
		$INOTIFY = { # usage: `use constant $PublicInbox::Syscall::INOTIFY'
			SYS_inotify_init1 => 332,
			SYS_inotify_add_watch => 292,
			SYS_inotify_rm_watch => 293,
		};
		$FS_IOC_GETFLAGS = 0x80046601;
		$FS_IOC_SETFLAGS = 0x40046602;
		$BTRFS_IOC_DEFRAG = 0x50009402;
	} elsif ($machine eq "x86_64") {
		$SYS_epoll_create = 213;
		$SYS_epoll_ctl = 233;
		$SYS_epoll_pwait //= 281;
		$SYS_renameat2 //= 316;
		$SYS_fstatfs = 138;
		$SYS_sendmsg = 46;
		$SYS_recvmsg = 47;
		$SYS_writev = 20;
		$INOTIFY = {
			SYS_inotify_init1 => 294,
			SYS_inotify_add_watch => 254,
			SYS_inotify_rm_watch => 255,
		};
		$FS_IOC_GETFLAGS = 0x80086601;
		$FS_IOC_SETFLAGS = 0x40086602;
		$BTRFS_IOC_DEFRAG = 0x50009402;
	} elsif ($machine eq 'x32') {
		$SYS_epoll_create = 1073742037;
		$SYS_epoll_ctl = 1073742057;
		$SYS_epoll_pwait //= 0x40000000 + 281;
		$SYS_renameat2 //= 0x40000000 + 316;
		$SYS_fstatfs = 0x40000000 + 138;
		$SYS_sendmsg = 0x40000206;
		$SYS_recvmsg = 0x40000207;
		$SYS_writev = 0x40000204;
		$FS_IOC_GETFLAGS = 0x80046601;
		$FS_IOC_SETFLAGS = 0x40046602;
		$INOTIFY = {
			SYS_inotify_init1 => 1073742118,
			SYS_inotify_add_watch => 1073742078,
			SYS_inotify_rm_watch => 1073742079,
		};
	} elsif ($machine eq 'sparc64') {
		$SYS_epoll_create = 193;
		$SYS_epoll_ctl = 194;
		$SYS_epoll_pwait //= 309;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 345;
		$SFD_CLOEXEC = 020000000;
		$SYS_fstatfs = 158;
		$SYS_sendmsg = 114;
		$SYS_recvmsg = 113;
		$FS_IOC_GETFLAGS = 0x40086601;
		$FS_IOC_SETFLAGS = 0x80086602;
	} elsif ($machine =~ m/^parisc/) { # untested, no machine on cfarm
		$SYS_epoll_create = 224;
		$SYS_epoll_ctl = 225;
		$SYS_epoll_pwait //= 297;
		$u64_mod_8 = 1;
		$SIGNUM{WINCH} = 23;
	} elsif ($machine =~ m/^ppc64/) {
		$SYS_epoll_create = 236;
		$SYS_epoll_ctl = 237;
		$SYS_epoll_pwait //= 303;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 357;
		$SYS_fstatfs = 100;
		$SYS_sendmsg = 341;
		$SYS_recvmsg = 342;
		$SYS_writev = 146;
		$FS_IOC_GETFLAGS = 0x40086601;
		$FS_IOC_SETFLAGS = 0x80086602;
		$INOTIFY = {
			SYS_inotify_init1 => 318,
			SYS_inotify_add_watch => 276,
			SYS_inotify_rm_watch => 277,
		};
	} elsif ($machine eq "ppc") { # untested, no machine on cfarm
		$SYS_epoll_create = 236;
		$SYS_epoll_ctl = 237;
		$SYS_epoll_pwait //= 303;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 357;
		$SYS_fstatfs = 100;
		$SYS_writev = 146;
		$FS_IOC_GETFLAGS = 0x40086601;
		$FS_IOC_SETFLAGS = 0x80086602;
	} elsif ($machine =~ m/^s390/) { # untested, no machine on cfarm
		$SYS_epoll_create = 249;
		$SYS_epoll_ctl = 250;
		$SYS_epoll_pwait //= 312;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 347;
		$SYS_fstatfs = 100;
		$SYS_sendmsg = 370;
		$SYS_recvmsg = 372;
		$SYS_writev = 146;
	} elsif ($machine eq 'ia64') { # untested, no machine on cfarm
		$SYS_epoll_create = 1243;
		$SYS_epoll_ctl = 1244;
		$SYS_epoll_pwait //= 1024 + 281;
		$u64_mod_8 = 1;
	} elsif ($machine eq "alpha") { # untested, no machine on cfarm
		# natural alignment, ints are 32-bits
		$SYS_epoll_create = 407;
		$SYS_epoll_ctl = 408;
		$SYS_epoll_pwait = 474;
		$u64_mod_8 = 1;
		$SFD_CLOEXEC = 010000000;
	} elsif ($machine =~ /\A(?:loong|a)arch64\z/ || $machine eq 'riscv64') {
		$SYS_epoll_create = 20; # (sys_epoll_create1)
		$SYS_epoll_ctl = 21;
		$SYS_epoll_pwait //= 22;
		$u64_mod_8 = 1;
		$no_deprecated = 1;
		$SYS_renameat2 //= 276;
		$SYS_fstatfs = 44;
		$SYS_sendmsg = 211;
		$SYS_recvmsg = 212;
		$SYS_writev = 66;
		$INOTIFY = {
			SYS_inotify_init1 => 26,
			SYS_inotify_add_watch => 27,
			SYS_inotify_rm_watch => 28,
		};
		$FS_IOC_GETFLAGS = 0x80086601;
		$FS_IOC_SETFLAGS = 0x40086602;
	} elsif ($machine =~ m/arm(v\d+)?.*l/) { # ARM OABI (untested on cfarm)
		$SYS_epoll_create = 250;
		$SYS_epoll_ctl = 251;
		$SYS_epoll_pwait //= 346;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 382;
		$SYS_fstatfs = 100;
		$SYS_sendmsg = 296;
		$SYS_recvmsg = 297;
		$SYS_writev = 146;
	} elsif ($machine =~ m/^mips64/) { # cfarm only has 32-bit userspace
		$SYS_epoll_create = 5207;
		$SYS_epoll_ctl = 5208;
		$SYS_epoll_pwait //= 5272;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 5311;
		$SYS_fstatfs = 5135;
		$SYS_sendmsg = 5045;
		$SYS_recvmsg = 5046;
		$SYS_writev = 5019;
		$FS_IOC_GETFLAGS = 0x40046601;
		$FS_IOC_SETFLAGS = 0x80046602;
	} elsif ($machine =~ m/^mips/) { # 32-bit, tested on mips64 cfarm host
		$SYS_epoll_create = 4248;
		$SYS_epoll_ctl = 4249;
		$SYS_epoll_pwait //= 4313;
		$u64_mod_8 = 1;
		$SYS_renameat2 //= 4351;
		$SYS_fstatfs = 4100;
		$SYS_sendmsg = 4179;
		$SYS_recvmsg = 4177;
		$SYS_writev = 4146;
		$FS_IOC_GETFLAGS = 0x40046601;
		$FS_IOC_SETFLAGS = 0x80046602;
		$SIGNUM{WINCH} = 20;
		$INOTIFY = {
			SYS_inotify_init1 => 4329,
			SYS_inotify_add_watch => 4285,
			SYS_inotify_rm_watch => 4286,
		};
	} else {
		warn <<EOM;
machine=$machine ptrsize=$Config{ptrsize} has no syscall definitions
git clone https://80x24.org/public-inbox.git and
Send the output of ./devel/sysdefs-list to meta\@public-inbox.org
EOM
	}
	if ($SYS_epoll_pwait) {
		if ($u64_mod_8) {
			*epoll_pwait = \&epoll_pwait_mod8;
			*epoll_ctl = \&epoll_ctl_mod8;
		} else {
			*epoll_pwait = \&epoll_pwait_mod4;
			*epoll_ctl = \&epoll_ctl_mod4;
		}
		push @EXPORT_OK, qw(epoll_pwait epoll_ctl);
	}
} elsif ($^O =~ /\A(?:freebsd|openbsd|netbsd|dragonfly)\z/) {
# don't use syscall.ph here, name => number mappings are not stable on *BSD
# but the actual numbers are.
# OpenBSD perl redirects syscall perlop to libc functions
# https://cvsweb.openbsd.org/src/gnu/usr.bin/perl/gen_syscall_emulator.pl
# https://www.netbsd.org/docs/internals/en/chap-processes.html#syscall_versioning
# https://wiki.freebsd.org/AddingSyscalls#Backward_compatibily
# (I'm assuming Dragonfly copies FreeBSD, here, too)
	$SYS_recvmsg = 27;
	$SYS_sendmsg = 28;
	$SYS_writev = 121;
}

BEGIN {
	if ($^O eq 'linux') {
		%CONST = (
			MSG_MORE => 0x8000,
			FIONREAD => 0x541b,
			TCP_ESTABLISHED => 1,
			TMPL_cmsg_len => TMPL_size_t,
			# cmsg_len, cmsg_level, cmsg_type
			SIZEOF_cmsghdr => SIZEOF_int * 2 + SIZEOF_size_t,
			CMSG_DATA_off => '',
			TMPL_msghdr => 'P' . # msg_name
				'L' . # msg_namelen (socklen_t)
				'@'.(2 * SIZEOF_ptr).'P'. # msg_iov
				TMPL_size_t. # msg_iovlen
				'@'.(4 * SIZEOF_ptr).'P'. # msg_control
				TMPL_size_t. # msg_controllen
				'i', # msg_flags
		);
	} elsif ($^O =~ /\A(?:freebsd|openbsd|netbsd|dragonfly)\z/) {
		%CONST = (
			TMPL_cmsg_len => 'L', # socklen_t
			FIONREAD => 0x4004667f,
			SIZEOF_cmsghdr => SIZEOF_int * 3,
			CMSG_DATA_off => SIZEOF_ptr == 8 ? '@16' : '',
			TMPL_msghdr => 'P' . # msg_name
				'L' . # msg_namelen (socklen_t)
				'@'.(2 * SIZEOF_ptr).'P'. # msg_iov
				'i'. # msg_iovlen
				'@'.(4 * SIZEOF_ptr).'P'. # msg_control
				'L'. # msg_controllen
				'i', # msg_flags

		);
		# *BSD uses `TCPS_ESTABLISHED', not `TCP_ESTABLISHED'
		# dragonfly uses TCPS_ESTABLISHED==5, but it lacks TCP_INFO,
		# so leave it unset on dfly
		$CONST{TCP_ESTABLISHED} = 4 if $^O ne 'dragonfly';

		# FIXME: see if NetBSD can bump this
		$CONST{MY_SEQPACKET_MAX} = 400 if $^O eq 'netbsd';
	}
	if ($^O eq 'freebsd' && $kver ge v15.0) {
		$INOTIFY = {
			IN_CLOEXEC => 0x100000, # different from Linux :P
			SYS___specialfd => 577,
			AT_FDCWD => -100, # XXX we may use elsewhere
			SPECIALFD_INOTIFY => 2,
			SYS_inotify_add_watch_at => 593,
			SYS_inotify_rm_watch => 594,
		}
	}
	$CONST{CMSG_ALIGN_size} = SIZEOF_size_t;
	$CONST{SIZEOF_cmsghdr} //= 0;
	$CONST{TMPL_cmsg_len} //= undef;
	$CONST{CMSG_DATA_off} //= undef;
	$CONST{TMPL_msghdr} //= undef;
	$CONST{MSG_MORE} //= 0;
	$CONST{FIONREAD} //= undef;

	# Linux accepts over 128K, but FreeBSD 15.0 recvmsg(2) seems capped
	# at 64K.  IOW, it splits the buffer across multiple recvmsg calls
	# even when the first call is sufficiently large and the corresponding
	# sendmsg(2) was a single send on a larger buffer.
	$CONST{MY_SEQPACKET_MAX} //= 65536;
}
# $Config{sig_count} is NSIG, so this is NSIG/8:
my $SIGSET_SIZE = int($Config{sig_count}/8);

# SFD_CLOEXEC is arch-dependent, so IN_CLOEXEC may be, too
$INOTIFY->{IN_CLOEXEC} //= 0x80000 if $INOTIFY;

sub epoll_create {
	syscall($SYS_epoll_create, $no_deprecated ? 0 : 100);
}

# epoll_ctl wrapper
# ARGS: (epfd, op, fd, events_mask)
sub epoll_ctl_mod4 {
	syscall($SYS_epoll_ctl, $_[0]+0, $_[1]+0, $_[2]+0,
		pack("LLL", $_[3], $_[2], 0));
}

sub epoll_ctl_mod8 {
	syscall($SYS_epoll_ctl, $_[0]+0, $_[1]+0, $_[2]+0,
		pack("LLLL", $_[3], 0, $_[2], 0));
}

# epoll_pwait wrapper
# ARGS: (epfd, maxevents, timeout (milliseconds), arrayref, sigmask)
#  arrayref: values modified to be [$fd, $event]
our $epoll_pwait_events = '';
our $epoll_pwait_size = 0;
sub epoll_pwait_mod4 {
	my ($epfd, $maxevents, $timeout_msec, $events, $oldset) = @_;
	# resize our static buffer if maxevents bigger than we've ever done
	if ($maxevents > $epoll_pwait_size) {
		$epoll_pwait_size = $maxevents;
		vec($epoll_pwait_events, $maxevents * 12 - 1, 8) = 0;
	}
	@$events = ();
	my $ct = syscall($SYS_epoll_pwait, $epfd, $epoll_pwait_events,
			$maxevents, $timeout_msec,
			$oldset ? ($$oldset, $SIGSET_SIZE) : (undef, 0));
	croak "epoll_pwait: $!" if $ct == -1 && $! != EINTR;
	for (0..$ct - 1) {
		# 12-byte struct epoll_event
		# 4 bytes uint32_t events mask (skipped, useless to us)
		# 8 bytes: epoll_data_t union (first 4 bytes are the fd)
		# So we skip the first 4 bytes and take the middle 4:
		$events->[$_] = unpack('L', substr($epoll_pwait_events,
							12 * $_ + 4, 4));
	}
}

sub epoll_pwait_mod8 {
	my ($epfd, $maxevents, $timeout_msec, $events, $oldset) = @_;

	# resize our static buffer if maxevents bigger than we've ever done
	if ($maxevents > $epoll_pwait_size) {
		$epoll_pwait_size = $maxevents;
		vec($epoll_pwait_events, $maxevents * 16 - 1, 8) = 0;
	}
	@$events = ();
	my $ct = syscall($SYS_epoll_pwait, $epfd, $epoll_pwait_events,
			$maxevents, $timeout_msec,
			$oldset ? ($$oldset, $SIGSET_SIZE) : (undef, 0));
	croak "epoll_pwait: $!" if $ct == -1 && $! != EINTR;
	for (0..$ct - 1) {
		# 16-byte struct epoll_event
		# 4 bytes uint32_t events mask (skipped, useless to us)
		# 4 bytes padding (skipped, useless)
		# 8 bytes epoll_data_t union (first 4 bytes are the fd)
		# So skip the first 8 bytes, take 4, and ignore the last 4:
		$events->[$_] = unpack('L', substr($epoll_pwait_events,
							16 * $_ + 8, 4));
	}
}

sub _rename_noreplace_racy ($$) {
	my ($old, $new) = @_;
	if (link($old, $new)) {
		warn "unlink $old: $!\n" if !unlink($old) && $! != ENOENT;
		1
	} else {
		undef;
	}
}

# TODO: support FD args?
sub rename_noreplace ($$) {
	my ($old, $new) = @_;
	if ($SYS_renameat2) { # RENAME_NOREPLACE = 1, AT_FDCWD = -100
		my $ret = syscall($SYS_renameat2, -100, $old, -100, $new, 1);
		if ($ret == 0) {
			1; # like rename() perlop
		} elsif ($! == ENOSYS || $! == EINVAL) {
			undef $SYS_renameat2;
			_rename_noreplace_racy($old, $new);
		} else {
			undef
		}
	} else {
		_rename_noreplace_racy($old, $new);
	}
}

sub is_btrfs ($) {
	my ($fh) = @_;
	my $buf = "\0" x 120;
	if (syscall($SYS_fstatfs // return, fileno($fh), $buf) != 0) {
		warn "fstatfs: $!\n";
		return;
	}
	my $f_type = unpack($FSWORD_T, $buf);
	$f_type == 0x9123683E; # BTRFS_SUPER_MAGIC
}

# returns "0 but true" on success, undef on noop, true != 0 on failure
sub defrag_file ($) {
	my ($file) = @_;
	open my $fh, '+<', $file or return;
	is_btrfs $fh or return;
	$BTRFS_IOC_DEFRAG //
		return warn 'BTRFS_IOC_DEFRAG undefined for architecture';
	ioctl $fh, $BTRFS_IOC_DEFRAG, 0;
}

# returns "0 but true" on success, undef on noop, true != 0 on failure
sub nodatacow_fh ($) {
	my ($fh) = @_;
	return unless is_btrfs $fh;

	$FS_IOC_GETFLAGS //
		return (undef, warn 'FS_IOC_GETFLAGS undefined for platform');
	ioctl($fh, $FS_IOC_GETFLAGS, my $buf = "\0\0\0\0") //
		return (undef, warn "FS_IOC_GETFLAGS: $!");
	my $attr = unpack('l!', $buf);
	return if ($attr & 0x00800000); # FS_NOCOW_FL;
	ioctl($fh, $FS_IOC_SETFLAGS, pack('l', $attr | 0x00800000)) //
		return (undef, warn "FS_IOC_SETFLAGS: $!");
}

# returns "0 but true" on success, undef on noop, true != 0 on failure
sub yesdatacow_fh ($) {
	my ($fh) = @_;
	return unless is_btrfs $fh;
	$FS_IOC_GETFLAGS //
		return (undef, warn 'FS_IOC_GETFLAGS undefined for platform');
	ioctl($fh, $FS_IOC_GETFLAGS, my $buf = "\0\0\0\0") //
		return (undef, warn "FS_IOC_GETFLAGS: $!");
	my $attr = unpack('l!', $buf);
	return unless ($attr & 0x00800000); # FS_NOCOW_FL;
	ioctl($fh, $FS_IOC_SETFLAGS, pack('l', $attr & ~0x00800000)) //
		return (undef, warn "FS_IOC_SETFLAGS: $!");
}

sub nodatacow_dir ($) {
	my ($f) = @_;
	if (open my $fh, '<', $f) {
		return nodatacow_fh($fh); # returns "0 but true" on success
	}
}

use constant \%CONST;
sub CMSG_ALIGN ($) { ($_[0] + CMSG_ALIGN_size - 1) & ~(CMSG_ALIGN_size - 1) }
use constant CMSG_ALIGN_SIZEOF_cmsghdr => CMSG_ALIGN(SIZEOF_cmsghdr);
sub CMSG_SPACE ($) { CMSG_ALIGN($_[0]) + CMSG_ALIGN_SIZEOF_cmsghdr }
sub CMSG_LEN ($) { CMSG_ALIGN_SIZEOF_cmsghdr + $_[0] }
use constant msg_controllen_max =>
	CMSG_SPACE(10 * SIZEOF_int) + SIZEOF_cmsghdr; # space for 10 FDs

sub sendmsg_retry ($) {
	return 1 if $!{EINTR};
	return unless ($!{ENOMEM} || $!{ENOBUFS} || $!{ETOOMANYREFS});
	return if $_[0]-- == 0;
	# n.b. `N & (power-of-two - 1)' is a faster `N % power-of-two'
	warn "# sleeping on sendmsg: $! ($_[0] tries left)\n" if !($_[0] & 15);
	select(undef, undef, undef, 0.1);
	1;
}

sub fd2io (@) { map { open my $fh, '+<&=', $_; $fh } @_ }

no warnings 'once';

if (defined($SYS_sendmsg) && defined($SYS_recvmsg)) {

*send_cmd4 = sub ($$$$;$) {
	my ($sock, $io, undef, $flags, $tries) = @_;
	my $iov = pack('P'.TMPL_size_t,
			$_[2] // NUL, length($_[2] // NUL) || 1);
	my $fd_space = scalar(@{$io //= []}) * SIZEOF_int;
	my $msg_controllen = CMSG_SPACE($fd_space);
	my $cmsghdr = pack(TMPL_cmsg_len .
			'LL' .  # cmsg_level, cmsg_type,
			CMSG_DATA_off.('i' x scalar(@$io)). # CMSG_DATA
			'@'.($msg_controllen - 1).'x1', # pad to space, not len
			CMSG_LEN($fd_space), # cmsg_len
			SOL_SOCKET, SCM_RIGHTS, # cmsg_{level,type}
			map { fileno $_ } @$io); # CMSG_DATA
	my $mh = pack(TMPL_msghdr,
			undef, 0, # msg_name, msg_namelen (unused)
			$iov, 1, # msg_iov, msg_iovlen
			$cmsghdr, # msg_control
			$msg_controllen,
			0); # msg_flags
	my $s;
	$tries //= -1;
	do {
		$s = syscall($SYS_sendmsg, fileno($sock), $mh, $flags);
	} while ($s < 0 && sendmsg_retry($tries));
	$s >= 0 ? $s : undef;
};

*recv_cmd4 = sub ($$$) {
	my ($sock, undef, $blen) = @_;
	vec($_[1] //= '', $blen - 1, 8) = 0;
	my $cmsghdr = "\0" x msg_controllen_max; # 10 * sizeof(int)
	my $iov = pack('P'.TMPL_size_t, $_[1], $blen);
	my $mh = pack(TMPL_msghdr,
			undef, 0, # msg_name, msg_namelen (unused)
			$iov, 1, # msg_iov, msg_iovlen
			$cmsghdr, # msg_control
			msg_controllen_max,
			0); # msg_flags
	my $r;
	do {
		$r = syscall($SYS_recvmsg, fileno($sock), $mh, 0);
	} while ($r < 0 && $!{EINTR});
	if ($r < 0) {
		$_[1] = '';
		return (undef);
	}
	substr($_[1], $r, length($_[1]), '');
	my @ret;
	if ($r > 0) {
		my $msg_flags = (unpack TMPL_msghdr, $mh)[-1];
		my ($clen, $lvl, $type, @fds) = unpack(TMPL_cmsg_len.
					'LL'. # cmsg_level, cmsg_type
					CMSG_DATA_off.'i*', # @fds
					$cmsghdr);
		if ($lvl == SOL_SOCKET && $type == SCM_RIGHTS) {
			$clen -= CMSG_ALIGN_SIZEOF_cmsghdr;
			@ret = fd2io(@fds[0..(($clen / SIZEOF_int) - 1)]);
		}
		($msg_flags & (MSG_CTRUNC|MSG_TRUNC)) and
			croak "recvmsg $blen => $r trunc ".
				sprintf('0x%0x', $msg_flags);
	}
	@ret;
};

*sendmsg_more = sub ($@) {
	my $sock = shift;
	my $iov = join('', map { pack 'P'.TMPL_size_t, $_, length } @_);
	my $mh = pack(TMPL_msghdr,
			undef, 0, # msg_name, msg_namelen (unused)
			$iov, scalar(@_), # msg_iov, msg_iovlen
			undef, 0, # msg_control, msg_controllen (unused),
			0); # msg_flags (unused)
	my $s;
	do {
		$s = syscall($SYS_sendmsg, fileno($sock), $mh, MSG_MORE);
	} while ($s < 0 && $!{EINTR});
	$s < 0 ? undef : $s;
};
}

if (defined($SYS_writev)) {
*writev = sub {
	my $fh = shift;
	my $iov = join('', map { pack 'P'.TMPL_size_t, $_, length } @_);
	my $w;
	do {
		$w = syscall($SYS_writev, fileno($fh), $iov, scalar(@_));
	} while ($w < 0 && $!{EINTR});
	$w < 0 ? undef : $w;
};
}

1;

=head1 WARRANTY

This is free software. IT COMES WITHOUT WARRANTY OF ANY KIND.

=head1 AUTHORS

Brad Fitzpatrick <brad@danga.com>
