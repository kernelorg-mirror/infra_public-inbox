# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# parent class for LeiImport, LeiConvert, LeiIndex
package PublicInbox::LeiInput;
use v5.12;
use autodie qw(open);
use PublicInbox::DS;
use PublicInbox::Git qw(git_exe);
use PublicInbox::Spawn qw(which popen_rd);
use PublicInbox::InboxWritable qw(eml_from_path);

# JMAP RFC 8621 4.1.1
# https://www.iana.org/assignments/imap-jmap-keywords/imap-jmap-keywords.xhtml
our @KW = (qw(seen answered flagged draft), # widely-compatible
	qw(forwarded), # IMAP + Maildir
	qw(phishing junk notjunk)); # rarely supported

# note: RFC 8621 states "Users may add arbitrary keywords to an Email",
# but is it good idea?  Stick to the system and reserved ones, for now.
# The widely-compatible ones map to IMAP system flags, Maildir flags
# and mbox Status/X-Status headers.
my %KW = map { $_ => 1 } @KW;
my $L_MAX = 244; # Xapian term limit - length('L')

# RFC 8621, sec 2 (Mailboxes) a "label" for us is a JMAP Mailbox "name"
# "Servers MAY reject names that violate server policy"
my %ERR = (
	L => sub {
		my ($label) = @_;
		length($label) >= $L_MAX and
			return "`$label' too long (must be <= $L_MAX)";
		$label =~ /[A-Z]/ and
			return "`$label' must be lowercase";
		$label =~ m{\A[a-z0-9_](?:[a-z0-9_\-\./\@,]*[a-z0-9])?\z} ?
			undef : "`$label' is invalid";
	},
	kw => sub {
		my ($kw) = @_;
		$KW{$kw} ? undef : <<EOM;
`$kw' is not one of: `seen', `flagged', `answered', `draft'
`junk', `notjunk', `phishing' or `forwarded'
EOM
	}
);

sub check_input_format ($;$) {
	my ($lei, $files) = @_;
	my $opt_key = 'in-format';
	my $fmt = $lei->{opt}->{$opt_key};
	if (!$fmt) {
		my $err = $files ? "regular file(s):\n@$files" : '--stdin';
		return $lei->fail("--$opt_key unset for $err");
	}
	return 1 if $fmt eq 'eml';
	require PublicInbox::MboxLock if $files;
	require PublicInbox::MboxReader;
	PublicInbox::MboxReader->reads($fmt) or
		return $lei->fail("--$opt_key=$fmt unrecognized");
	1;
}

sub input_mbox_cb { # base MboxReader callback
	my ($eml, $self) = @_;
	$eml->header_set($_) for (qw(Status X-Status));
	$self->input_eml_cb($eml);
}

sub input_maildir_cb {
	my ($fn, $kw, $eml, $self) = @_;
	$self->input_eml_cb($eml);
}

sub input_mh_cb {
	my ($dn, $n, $kw, $eml, $self) = @_;
	$self->input_eml_cb($eml);
}

sub input_net_cb { # imap_each, nntp_each cb
	my ($url, $uid, $kw, $eml, $self) = @_;
	$self->input_eml_cb($eml);
}

# import a single file handle of $name
# Subclass must define ->input_eml_cb and ->input_mbox_cb
sub input_fh {
	my ($self, $ifmt, $fh, $name, @args) = @_;
	if ($ifmt eq 'eml') {
		my $buf = eval { PublicInbox::IO::read_all $fh, 0 };
		my $e = $@;
		return $self->{lei}->child_error($?, <<"") if !$fh->close || $e;
error reading $name: $! (\$?=$?) (\$@=$e)

		PublicInbox::Eml::strip_from($buf);

		# a user may feed just a body: git diff | lei rediff -U9
		if ($self->{-force_eml}) {
			my $eml = PublicInbox::Eml->new($buf);
			substr($buf, 0, 0) = "\n\n" if !$eml->{bdy};
		}
		$self->input_eml_cb(PublicInbox::Eml->new(\$buf), @args);
	} else {
		# prepare_inputs already validated $ifmt
		my $cb = PublicInbox::MboxReader->reads($ifmt) //
				die "BUG: bad fmt=$ifmt";
		$cb->(undef, $fh, $self->can('input_mbox_cb'), $self, @args);
	}
}

# handles mboxrd endpoints described in Documentation/design_notes.txt
sub handle_http_input ($$@) {
	my ($self, $url, @args) = @_;
	my $lei = $self->{lei} or die 'BUG: {lei} missing';
	my $curl_opt = delete $self->{"-curl-$url"} or
				die("BUG: $url curl options not prepared");
	my $uri = pop @$curl_opt;
	my $curl = PublicInbox::LeiCurl->new($lei, $self->{curl}) or return;
	push @$curl, '-s', @$curl_opt;
	my $cmd = $curl->for_uri($lei, $uri);
	$lei->qerr("# $cmd");
	my $rd = popen_rd($cmd, undef, { 2 => $lei->{2} });
	my $fh = grep(/\A--compressed\z/, @$curl) ? $rd :
		IO::Uncompress::Gunzip->new($rd, MultiStream => 1);
	eval { $self->input_fh('mboxrd', $fh, $url, @args) };
	my $err = $@ ? ": $@" : '';
	$rd->close if $rd->opened; # Gunzip won't close $rd on errors
	$lei->child_error($?, "@$cmd failed$err") if $err || $?;
}

sub oid2eml { # git->cat_async cb
	my ($bref, $oid, $type, $size, $self) = @_;
	if ($type eq 'blob') {
		$self->input_eml_cb(PublicInbox::Eml->new($bref));
	} else {
		warn "W: $oid is type=$type\n";
	}
}

sub each_ibx_eml_unindexed {
	my ($self, $ibx, @args) = @_;
	$ibx->isa('PublicInbox::Inbox') or return $self->{lei}->fail(<<EOM);
unindexed extindex $ibx->{topdir} not supported
EOM
	require PublicInbox::SearchIdx;
	my $n = $ibx->max_git_epoch;
	my @g = defined($n) ? map { $ibx->git_epoch($_) } (0..$n) : ($ibx->git);
	my $sidx = { D => {}, ibx => $ibx }; # D => {} filters out deletes
	my ($f, $at, $ct, $oid, $cmt);
	for my $git (grep defined, @g) {
		my $s = PublicInbox::SearchIdx::log2stack($sidx, $git, 'HEAD');
		while (($f, $at, $ct, $oid, $cmt) = $s->pop_rec) {
			$git->cat_async($oid, \&oid2eml, $self) if $f eq 'm';
		}
		$git->cleanup; # wait all
	}
}

sub each_ibx_eml {
	my ($self, $ibx, @args) = @_; # TODO: is @args used at all?
	my $over = $ibx->over or return each_ibx_eml_unindexed(@_);
	my $git = $ibx->git;
	my $prev = 0;
	my $smsg;
	my $ids = $over->ids_after(\$prev);
	while (@$ids) {
		for (@$ids) {
			$smsg = $over->get_art($_) // next;
			$git->cat_async($smsg->{blob}, \&oid2eml, $self);
		}
		$ids = $over->ids_after(\$prev);
	}
	$git->cat_async_wait;
}

sub input_path_url {
	my ($self, $input, @args) = @_;
	my $lei = $self->{lei};
	my $ifmt = lc($lei->{opt}->{'in-format'} // '');
	# TODO auto-detect?
	if ($input =~ m!\Aimaps?://!i) {
		$lei->{net}->imap_each($input, $self->can('input_net_cb'),
						$self, @args);
		return;
	} elsif ($input =~ m!\A(?:nntps?|s?news)://!i) {
		$lei->{net}->nntp_each($input, $self->can('input_net_cb'),
						$self, @args);
		return;
	} elsif ($input =~ m!\Ahttps?://!i) {
		handle_http_input($self, $input, @args);
		return;
	}

	# local-only below
	my $ifmt_pfx = '';
	if ($input =~ s!\A([a-z0-9]+):!!i) {
		$ifmt_pfx = "$1:";
		$ifmt = lc($1);
	} elsif ($input =~ /\.(?:patch|eml)\z/i) {
		$ifmt = 'eml';
	} elsif ($input =~ m{\A(?:.+)/(?:new|cur)/([^/]+)\z} && -f $input) {
		my $bn = $1;
		my $fl = PublicInbox::MdirReader::maildir_basename_flags($bn);
		return if index($fl, 'T') >= 0;
		return $self->pmdir_cb($input, $fl) if $self->can('pmdir_cb');
		my $eml = eml_from_path($input) or return
			$lei->qerr("# $input not readable");
		my $kw = PublicInbox::MdirReader::flags2kw($fl);
		$self->can('input_maildir_cb')->($input, $kw, $eml, $self);
		return;
	}
	my $devfd = $lei->path_to_fd($input) // return;
	if ($devfd >= 0) {
		$self->input_fh($ifmt, $lei->{$devfd}, $input, @args);
	} elsif ($devfd < 0 && $input =~ m{\A(.+/)([0-9]+)\z} && -f $input) {
		my ($dn, $n) = ($1, $2);
		my $mhr = PublicInbox::MHreader->new($dn, $lei->{3});
		$mhr->mh_read_one($n, $self->can('input_mh_cb'), $self);
	} elsif (-f $input && $ifmt eq 'eml') {
		open my $fh, '<', $input; # autodie::open hits caller eval
		$self->input_fh($ifmt, $fh, $input, @args);
	} elsif (-f _) {
		my $m = $lei->{opt}->{'lock'} //
			PublicInbox::MboxLock->defaults;
		my $mbl = PublicInbox::MboxLock->acq($input, 0, $m);
		my $zsfx = PublicInbox::MboxReader::zsfx($input);
		if ($zsfx) {
			my $in = delete $mbl->{fh};
			$mbl->{fh} =
			     PublicInbox::MboxReader::zsfxcat($in, $zsfx, $lei);
		}
		local $PublicInbox::DS::in_loop = 0 if $zsfx; # awaitpid
		$self->input_fh($ifmt, $mbl->{fh}, $input, @args);
	} elsif (-d _ && $ifmt eq 'maildir') {
		my $mdr = PublicInbox::MdirReader->new;
		if (my $pmd = $self->{pmd}) {
			$mdr->maildir_each_file($input,
						$pmd->can('each_mdir_fn'),
						$pmd, @args);
		} else {
			$mdr->maildir_each_eml($input,
						$self->can('input_maildir_cb'),
						$self, @args);
		}
	} elsif (-d _ && $ifmt eq 'mh') {
		my $mhr = PublicInbox::MHreader->new($input.'/', $lei->{3});
		$mhr->{sort} = $lei->{opt}->{sort} // [ 'sequence'];
		$mhr->mh_each_eml($self->can('input_mh_cb'), $self, @args);
	} elsif (-d _ && $ifmt =~ /\A(?:v1|v2)\z/) {
		my $ibx = PublicInbox::Inbox->new({inboxdir => $input});
		each_ibx_eml($self, $ibx, @args);
	} elsif (-d _ && $ifmt eq 'extindex') {
		my $esrch = PublicInbox::ExtSearch->new($input);
		each_ibx_eml($self, $esrch, @args);
	} elsif ($self->{missing_ok} && !-e $input) { # don't ->fail
		if ($lei->{cmd} eq 'p2q') {
			my $fp = [ git_exe, qw(format-patch --stdout -1),
					$input ];
			my $rdr = { 2 => $lei->{2} };
			my $fh = popen_rd($fp, undef, $rdr);
			eval { $self->input_fh('eml', $fh, $input, @args) };
			my $err = $@ ? ": $@" : '';
			$lei->child_error($?, "@$fp failed$err") if $err || $?;
		} else {
			$self->folder_missing("$ifmt:$input");
		}
	} else {
		$lei->fail("$ifmt_pfx$input unsupported (TODO)");
	}
}

# subclasses should overrride this (see LeiRefreshMailSync)
sub folder_missing { die "BUG: ->folder_missing undefined for $_[0]" }

sub bad_http ($$;$) {
	my ($lei, $url, $alt) = @_;
	my $x = $alt ? "did you mean <$alt>?" : 'download and import manually';
	$lei->fail("E: <$url> not recognized, $x");
}

sub prepare_http_input ($$$) {
	my ($self, $lei, $url) = @_;
	require URI;
	require PublicInbox::MboxReader;
	require PublicInbox::LeiCurl;
	require IO::Uncompress::Gunzip;
	$self->{curl} //= which('curl') or
				return $lei->fail("curl missing for <$url>");
	my $uri = URI->new($url);
	my $path = $uri->path;
	my %qf = $uri->query_form;
	my @curl_opt;
	if ($path =~ m!/(?:t\.mbox\.gz|all\.mbox\.gz)\z!) {
		# OK
	} elsif ($path =~ m!/raw\z!) {
		push @curl_opt, '--compressed';
	# convert search query to mboxrd request since they require POST
	# this is only intended for PublicInbox::WWW, and will false-positive
	# on many other search engines... oh well
	} elsif (defined $qf{'q'}) {
		$qf{x} = 'm';
		$uri->query_form(\%qf);
		push @curl_opt, '-d', '';
		$$uri ne $url and $lei->qerr(<<"");
# <$url> rewritten to <$$uri> with HTTP POST

	# try to provide hints for /$INBOX/$MSGID/T/ and /$INBOX/
	} elsif ($path =~ s!/[tT]/\z!/t.mbox.gz! ||
			$path =~ s!/t\.atom\z!/t.mbox.gz! ||
			$path =~ s!/([^/]+\@[^/]+)/\z!/$1/raw!) {
		$uri->path($path);
		return bad_http($lei, $url, $$uri);
	} else {
		return bad_http($lei, $url);
	}
	$self->{"-curl-$url"} = [ @curl_opt, $uri ]; # for handle_http_input
}

sub add_dir ($$$$) {
	my ($lei, $istate, $ifmt, $input) = @_;
	if ($istate->{-may_sync}) {
		$$input = "$ifmt:".$lei->abs_path($$input);
		push @{$istate->{-sync}->{ok}}, $$input if $istate->{-sync};
	} else {
		substr($$input, 0, 0) = "$ifmt:"; # prefix
	}
	push @{$istate->{$ifmt}}, $$input;
}

sub prepare_inputs { # returns undef on error
	my ($self, $lei, $inputs) = @_;
	my $in_fmt = $lei->{opt}->{'in-format'};
	my $sync = $lei->{opt}->{'mail-sync'} ? {} : undef; # using LeiMailSync
	my $may_sync = $sync || $self->{-mail_sync};
	if ($lei->{opt}->{stdin}) {
		@$inputs and return
			$lei->fail("--stdin and @$inputs do not mix");
		check_input_format($lei) or return;
		push @$inputs, '/dev/stdin';
		push @{$sync->{no}}, '/dev/stdin' if $sync;
	}
	my $net = $lei->{net}; # NetWriter may be created by l2m
	my @f;
	my $istate = { -sync => $sync, -may_sync => $may_sync };
	# e.g. Maildir:/home/user/Mail/ or imaps://example.com/INBOX
	for my $input (@$inputs) {
		my $input_path = $input;
		if ($input =~ m!\A(?:imaps?|nntps?|s?news)://!i) {
			require PublicInbox::NetReader;
			$net //= PublicInbox::NetReader->new;
			$net->add_url($input, $self->{-ls_ok});
			push @{$sync->{ok}}, $input if $sync;
		} elsif ($input_path =~ m!\Ahttps?://!i) { # mboxrd.gz
			# TODO: how would we detect r/w JMAP?
			push @{$sync->{no}}, $input if $sync;
			prepare_http_input($self, $lei, $input_path) or return;
		} elsif ($input =~ /\A(?:L|kw):/) {
			return $lei->fail("Unable to handle `$input', ".
					"did you mean `+$input' ?");
		} elsif ($input_path =~ s/\A([a-z0-9]+)://is) {
			my $ifmt = lc $1;
			if (($in_fmt // $ifmt) ne $ifmt) {
				return $lei->fail(<<"");
--in-format=$in_fmt and `$ifmt:' conflict

			}
			($sync && $ifmt !~ /\A(?:maildir|mh)\z/i) and
				push(@{$sync->{no}}, $input);
			my $devfd = $lei->path_to_fd($input_path) // return;
			if ($devfd >= 0 || (-f $input_path || -p _)) {
				require PublicInbox::MboxLock;
				require PublicInbox::MboxReader;
				PublicInbox::MboxReader->reads($ifmt) or return
					$lei->fail("$ifmt not supported");
			} elsif (-d $input_path) { # TODO extindex
				$ifmt =~ /\A(?:maildir|mh|v1|v2|extindex)\z/ or
					return$lei->fail("$ifmt not supported");
				$input = $input_path;
				add_dir $lei, $istate, $ifmt, \$input;
			} elsif ($self->{missing_ok} &&
					$ifmt =~ /\A(?:maildir|mh)\z/ &&
					!-e $input_path) {
				# for "lei rm-watch" on missing Maildir
				$may_sync and $input = "$ifmt:".
						$lei->abs_path($input_path);
			} else {
				return $lei->fail("Unable to handle $input");
			}
		} elsif ($input =~ /\.(?:eml|patch)\z/i && -f $input) {
			lc($in_fmt//'eml') eq 'eml' or return $lei->fail(<<"");
$input is `eml', not --in-format=$in_fmt

			push @{$sync->{no}}, $input if $sync;
		} elsif ($input =~ m{\A(.+)/(new|cur)/([^/]+)\z} && -f $input) {
			# single file in a Maildir
			my ($mdir, $nc, $bn) = ($1, $2, $3);
			my $other = $mdir . ($nc eq 'new' ? '/cur' : '/new');
			return $lei->fail(<<EOM) if !-d $other;
No `$other' directory for `$input'
EOM
			lc($in_fmt//'eml') eq 'eml' or return $lei->fail(<<"");
$input is `eml', not --in-format=$in_fmt

			if ($sync) {
				$input = $lei->abs_path($mdir) . "/$nc/$bn";
				push @{$sync->{ok}}, $input;
			}
			require PublicInbox::MdirReader;
		} else {
			my $devfd = $lei->path_to_fd($input) // return;
			if ($devfd < 0 && $input =~ m{\A(.+)/([0-9]+)\z} &&
					-f $input) { # single file in MH dir
				my ($mh, $n) = ($1, $2);
				lc($in_fmt//'eml') eq 'eml' or
						return $lei->fail(<<"");
$input is `eml', not --in-format=$in_fmt

				if ($sync) {
					$input = $lei->abs_path($mh)."/$n";
					push @{$sync->{ok}}, $input;
				}
				require PublicInbox::MHreader;
			} elsif ($devfd >= 0 || -f $input || -p _) {
				push @{$sync->{no}}, $input if $sync;
				push @f, $input;
			} elsif (-d "$input/new" && -d "$input/cur") {
				add_dir $lei, $istate, 'maildir', \$input;
			} elsif (-e "$input/inbox.lock") {
				add_dir $lei, $istate, 'v2', \$input;
			} elsif (-e "$input/ssoma.lock") {
				add_dir $lei, $istate, 'v1', \$input;
			} elsif (-e "$input/ei.lock") {
				add_dir $lei, $istate, 'extindex', \$input;
			} elsif (-f "$input/.mh_sequences") {
				add_dir $lei, $istate, 'mh', \$input;
			} elsif ($self->{missing_ok} && !-e $input) {
				if ($lei->{cmd} eq 'p2q') {
					# will run "git format-patch"
				} elsif ($may_sync) { # for lei rm-watch
					# FIXME: support MH, here
					$input = 'maildir:'.
						$lei->abs_path($input);
				}
			} else {
				return $lei->fail("Unable to handle $input")
			}
		}
	}
	if (@f) { check_input_format($lei, \@f) or return }
	if ($sync && $sync->{no}) {
		return $lei->fail(<<"") if !$sync->{ok};
--mail-sync specified but no inputs support it

		# non-fatal if some inputs support support sync
		warn("# --mail-sync will only be used for @{$sync->{ok}}\n");
		warn("# --mail-sync is not supported for: @{$sync->{no}}\n");
	}
	if ($net) {
		$net->{-can_die} = 1;
		if (my $err = $net->errors($lei)) {
			return $lei->fail($err);
		}
		$net->{quiet} = $lei->{opt}->{quiet};
		require PublicInbox::LeiAuth;
		$lei->{auth} //= PublicInbox::LeiAuth->new;
		$lei->{net} //= $net;
	}
	if (my $md = $istate->{maildir}) {
		require PublicInbox::MdirReader;
		if ($self->can('pmdir_cb')) {
			require PublicInbox::LeiPmdir;
			$self->{pmd} = PublicInbox::LeiPmdir->new($lei, $self);
		}
		grep(!m!\Amaildir:/!i, @$md) and die "BUG: @$md (no pfx)";

		# start watching Maildirs ASAP
		if ($may_sync && $lei->{sto}) {
			$lei->lms(1)->lms_write_prepare->add_folders(@$md);
			$lei->refresh_watches;
		}
	}
	if (my $mh = $istate->{mh}) {
		require PublicInbox::MHreader;
		grep(!m!\Amh:!i, @$mh) and die "BUG: @$mh (no pfx)";
		if ($may_sync && $lei->{sto}) {
			$lei->lms(1)->lms_write_prepare->add_folders(@$mh);
			# $lei->refresh_watches; TODO
		}
	}
	require PublicInbox::ExtSearch if $istate->{extindex};
	$self->{inputs} = $inputs;
}

sub process_inputs {
	my ($self) = @_;
	my $err;
	for my $input (@{$self->{inputs}}) {
		eval { $self->input_path_url($input) };
		next unless $@;
		$err = "$input: $@";
		last;
	}
	# always commit first, even on error partial work is acceptable for
	# lei <import|tag|convert>
	$self->{lei}->sto_barrier_request;
	$self->{lei}->fail($err) if $err;
}

sub input_only_atfork_child {
	my ($self) = @_;
	my $lei = $self->{lei};
	$lei->_lei_atfork_child;
	PublicInbox::IPC::ipc_atfork_child($self);
	$lei->{auth}->do_auth_atfork($self) if $lei->{auth};
	undef;
}

# alias this as "net_merge_all_done" to use as an LeiAuth callback
sub input_only_net_merge_all_done {
	my ($self) = @_;
	$self->wq_io_do('process_inputs');
	$self->wq_close;
}

# like Getopt::Long, but for +kw:FOO and -kw:FOO to prepare
# for update_xvmd -> update_vmd
# returns something like { "+L" => [ @Labels ], ... }
sub vmd_mod_extract {
	my ($lei, $argv) = @_;
	my (@new_argv, @err);
	for my $x (@$argv) {
		if ($x =~ /\A(\+|\-)(kw|L):(.+)\z/) {
			my ($op, $pfx, $val) = ($1, $2, $3);
			if (my $err = $ERR{$pfx}->($val)) {
				push @err, $err;
			} else { # set "+kw", "+L", "-L", "-kw"
				push @{$lei->{vmd_mod}->{$op.$pfx}}, $val;
			}
		} else {
			push @new_argv, $x;
		}
	}
	@$argv = @new_argv;
	@err;
}

1;
