# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>
# based on notmuch, but with no concept of folders, files
#
# Indexes mail with Xapian and our (SQLite-based) ::Msgmap for use
# with the web and NNTP interfaces.  This index maintains thread
# relationships for use by PublicInbox::SearchThread.
# This writes to the search index.
package PublicInbox::SearchIdx;
use strict;
use v5.10.1;
use parent qw(PublicInbox::Search PublicInbox::Lock PublicInbox::Umask
	Exporter);
use autodie qw(closedir opendir rename);
use PublicInbox::Eml;
use PublicInbox::DS qw(now);
use PublicInbox::Search qw(xap_terms);
use PublicInbox::Syscall qw(defrag_file);
use PublicInbox::InboxWritable;
use PublicInbox::MID qw(mids_for_index mids);
use PublicInbox::MsgIter;
use PublicInbox::IdxStack;
use Carp qw(croak carp);
use POSIX qw(strftime);
use Fcntl qw(SEEK_SET);
use Time::Local qw(timegm);
use PublicInbox::OverIdx;
use PublicInbox::Spawn qw(run_wait popen_rd);
use PublicInbox::Git qw(git_unquote);
use PublicInbox::MsgTime qw(msg_timestamp msg_datestamp);
use PublicInbox::Address;
use File::Glob qw(bsd_glob GLOB_NOSORT);
use File::Path ();
use File::Spec ();
use Config;
our @EXPORT_OK = qw(log2stack is_ancestor check_size prepare_stack
	index_text term_generator add_val is_bad_blob update_checkpoint
	add_bool_term xap_wdb);
my $X = \%PublicInbox::Search::X;
our ($DB_CREATE_OR_OPEN, $DB_OPEN);
our $DB_NO_SYNC = 0;
our $DB_DANGEROUS = 0;
our $CHECKPOINT_INTVL = 15; # seconds
our $DEFRAG_NR = 100000; # document count
our $SHARD_SPLIT_AT = 100000; # document count
our $BATCH_BYTES = $ENV{XAPIAN_FLUSH_THRESHOLD} ? 0x7fffffff :
	# assume a typical 64-bit system has 8x more RAM than a
	# typical 32-bit system:
	(($Config{ptrsize} >= 8 ? 8192 : 1024) * 1024);
use constant {
	DEBUG => !!$ENV{DEBUG},
	MAX_TERM_SIZE => 245, # Xapian limitation, includes prefix
};
my $BASE85 = qr/[a-zA-Z0-9\!\#\$\%\&\(\)\*\+\-;<=>\?\@\^_`\{\|\}\~]+/;
my $xapianlevels = qr/\A(?:full|medium)\z/;
my $hex = '[a-f0-9]';
my $OID = $hex .'{40,}';
my @VMD_MAP = (kw => 'K', L => 'L'); # value order matters
our $INDEXLEVELS = qr/\A(?:full|medium|basic)\z/;
our $PATCHID_BROKEN;

sub new {
	my ($class, $ibx, $creat_opt, $shard) = @_;
	ref $ibx or die "BUG: expected PublicInbox::Inbox object: $ibx";
	my $inboxdir = $ibx->{inboxdir};
	my $version = $ibx->version;
	my $indexlevel = 'full';
	if ($ibx->{indexlevel}) {
		if ($ibx->{indexlevel} =~ $INDEXLEVELS) {
			$indexlevel = $ibx->{indexlevel};
		} else {
			die("Invalid indexlevel $ibx->{indexlevel}\n");
		}
	}
	undef $PATCHID_BROKEN; # retry on new instances in case of upgrades
	$ibx = PublicInbox::InboxWritable->new($ibx);
	my $self = PublicInbox::Search->new($ibx);
	bless $self, $class;
	$self->{ibx} = $ibx;
	$self->load_extra_indexers($ibx);
	$self->{indexlevel} = $indexlevel;
	$self->{-set_indexlevel_once} = 1 if $indexlevel eq 'medium';
	if ($ibx->{-skip_docdata}) {
		$self->{-set_skip_docdata_once} = 1;
		$self->{-skip_docdata} = 1;
	}
	if ($version == 1) {
		$self->{lock_path} = "$inboxdir/ssoma.lock";
		$self->{oidx} = PublicInbox::OverIdx->new(
				"$self->{xpfx}/over.sqlite3", $creat_opt);
	} elsif ($version == 2) {
		defined $shard or die "shard is required for v2\n";
		# shard is a number
		$self->{shard} = $shard;
		$self->{lock_path} = undef;
	} else {
		die "unsupported inbox version=$version\n";
	}
	$self->{creat} = !!$creat_opt; # TODO: eliminate
	$self->{-opt} = $creat_opt;
	$self;
}

sub need_xapian ($) { ($_[0]->{indexlevel} // 'full') =~ $xapianlevels }

sub du_1_level (@) {
	my $s = 0;
	for my $d (@_) {
		$s += (-s $_ // 0) for bsd_glob("$d/*", GLOB_NOSORT);
	}
	$s;
}

sub join_splits ($) {
	my ($self) = @_;
	require PublicInbox::Xapcmd;
	my ($cmd, undef) = PublicInbox::Xapcmd::compact_cmd($self->{-opt});
	my $xpfx = $self->{xpfx};
	opendir(my $dh, $xpfx);
	my $shard = $self->{shard} // '';
	my @tmps = grep /\A$shard\.[0-9]+\.tmp\z/, readdir($dh);
	closedir $dh;
	@tmps or return warn("BUG? no $shard.*.tmps to join in $xpfx\n");
	$_ = ((split /\./, $_)[1] + 0) for @tmps; # Schwartzian transform
	@tmps = sort { $a <=> $b } @tmps;
	$_ = "$shard.$_.tmp" for @tmps; # undo transform

	my $pr = $self->{-opt}->{-progress};
	my @ftmps = map { "$xpfx/$_" } @tmps;
	my ($before_bytes, $t0);
	my $xdir = $self->xdir;

	my $rdr = { -C => $xpfx };
	my $wip = File::Temp->newdir("$shard.join-tmp-XXXX", DIR => $xpfx);
	my $dst = File::Spec->rel2abs($wip->dirname . "/$shard");
	# use relative paths for cmd to reduce likelyhood of running out of
	# argv space
	push @$cmd, $self->{shard}, @tmps, File::Spec->abs2rel($dst, $xpfx);
	$self->{-opt}->{cow} or PublicInbox::Syscall::nodatacow_dir($dst);
	my $restore = $self->with_umask;
	if ($pr) {
		$pr->("$shard compacting (@$cmd) (in $xpfx)\n");
		$before_bytes = du_1_level $xdir, @ftmps;
		$t0 = now;
	}
	my $rd = popen_rd $cmd, undef, $rdr;
	while (<$rd>) {
		$pr or next;
		s/\r/\r# $shard /g;
		$pr->("# $shard $_");
	}
	$rd->close or die "@$cmd failed: \$?=$?\n";
	File::Path::remove_tree(@ftmps);
	my $owner = $self->{ibx} // $self->{eidx} // $self;
	my $unlk = PublicInbox::Lock->new($owner->open_lock)->lock_for_scope;
	if (-e $xdir) {
		rename $xdir, "$dst/old";
	} else {
		warn "W: $xdir gone ($!), attempting to replace anyways...\n";
	}
	rename $dst, $xdir;
	undef $unlk;
	File::Path::remove_tree("$xdir/old");
	return if !$pr;
	my $after_bytes = du_1_level $xdir;
	my $diff = now - $t0;
	$pr->("$shard compact took ",
		sprintf('%0.1fs, %0.1fMB => %0.1fMB',
			$diff, $before_bytes >> 20, $after_bytes >> 20), "\n");
}

sub idx_release {
	my ($self, $wake) = @_;
	if (need_xapian($self)) {
		my $djs = delete $self->{-do_join_splits};
		delete $self->{-doc_max};
		my $xdb = delete $self->{xdb} or croak 'BUG: {xdb} missing';
		if ($djs) {
			$xdb->begin_transaction;
			$xdb->set_metadata('split-at', '');
			$xdb->commit_transaction;
		}
		$xdb->close;
		delete $self->{-xdb_tmp} and croak 'BUG: {-xdb_tmp} exists';
		join_splits($self) if $djs && delete($self->{-splits_dirty});
	}
	$self->lock_release($wake) if $self->{creat};
	undef;
}

sub load_xapian_writable () {
	return 1 if $X->{WritableDatabase};
	PublicInbox::Search::load_xapian() or die "failed to load Xapian: $@\n";
	my $xap = $PublicInbox::Search::Xap;
	for (qw(Document TermGenerator WritableDatabase)) {
		$X->{$_} = $xap.'::'.$_;
	}
	eval 'require '.$X->{WritableDatabase} or die;
	*sortable_serialise = $xap.'::sortable_serialise';
	$DB_CREATE_OR_OPEN = eval($xap.'::DB_CREATE_OR_OPEN()');
	$DB_OPEN = eval($xap.'::DB_OPEN()');
	my $ver = eval 'v'.join('.', eval($xap.'::major_version()'),
				eval($xap.'::minor_version()'),
				eval($xap.'::revision()'));
	if ($ver ge v1.4) { # new flags in Xapian 1.4
		$DB_NO_SYNC = 0x4;
		$DB_DANGEROUS = 0x10;
	}
	# Xapian v1.2.21..v1.2.24 were missing close-on-exec on OFD locks
	$X->{CLOEXEC_UNSET} = 1 if $ver ge v1.2.21 && $ver le v1.2.24;
	1;
}

sub xap_wdb ($$;$$) {
	my ($dir, $flags, $opt, $self) = @_;
	my (@arg, $bs);
	if (!($flags & $DB_OPEN) && ($bs = $opt->{'block-size'})) {
		if ($PublicInbox::Search::Xap eq 'Xapian') {
			@arg = ($bs);
		} else {
			warn <<EOM if !$opt->{-block_size_warned}++;
--block-size=$arg[0] is not supported by `Search::Xapian' XS bindings;
newer `Xapian' SWIG bindings are required.
EOM
		}
	}
	my $xdb = eval { $X->{WritableDatabase}->new($dir, $flags, @arg) };
	croak "Failed opening $dir: $@" if $@;
	$xdb;
}

sub idx_acquire {
	my ($self) = @_;
	my $flag;
	my $dir = $self->xdir;
	if (need_xapian($self)) {
		croak 'already acquired' if $self->{xdb};
		load_xapian_writable();
		$flag = $self->{creat} ? $DB_CREATE_OR_OPEN : $DB_OPEN;
	}
	my $owner = $self->{ibx} // $self->{eidx} // $self;
	if ($self->{creat}) {
		$self->lock_acquire;

		# don't create empty Xapian directories if we don't need Xapian
		my $is_shard = defined($self->{shard});
		if (!-d $dir && (!$is_shard ||
				($is_shard && need_xapian($self)))) {
			File::Path::mkpath($dir);
			$self->{-opt}->{cow} or
				PublicInbox::Syscall::nodatacow_dir($dir);
			open my $fh, '>>', $owner->open_lock;
			# owner == self for CodeSearchIdx
			$self->{-set_has_threadid_once} = 1 if $owner != $self;
			$flag |= $DB_DANGEROUS if $self->{-opt}->{dangerous};
		}
	}
	return unless defined $flag;
	$flag |= $DB_NO_SYNC if !$self->{-opt}->{fsync};
	my $xdb = xap_wdb $dir, $flag, $self->{-opt}, $self;
	$xdb->begin_transaction;
	my $cur = $xdb->get_metadata('split-at');
	if ($cur || $self->{-opt}->{'split-shards'}) {
		my $new = $self->{-opt}->{'split-at'};
		# respect in-progress value (XXX incomplete, delay until 3.x)
		# this doesn't work if new/old public-inbox versions mix,
		# so we currently disable {ckpt_unlocks} if using split-at
		if ($cur) {
			$new && $new != $cur and warn <<EOM;
W: using existing --split-at=$cur
EOM
			$self->{-do_join_splits} or warn <<EOM;
W: PID:$$ will not join split shards
EOM
			$self->{-opt}->{'split-at'} = $cur;
		} else {
			$cur ||= $new // $SHARD_SPLIT_AT;
			$xdb->set_metadata('split-at', "$cur");
			$self->{-do_join_splits} = 1;
		}
		$self->{-doc_max} = $xdb->get_lastdocid || $cur;
	}
	($self->{-do_join_splits} || $self->{-opt}->{dangerous}) ?
			$xdb->commit_transaction : $xdb->cancel_transaction;
	$self->{xdb} = $xdb;
}

sub add_val ($$$) {
	my ($doc, $col, $num) = @_;
	$num = sortable_serialise($num);
	$doc->add_value($col, $num);
}

sub term_generator ($) { # write-only
	my ($self) = @_;

	$self->{term_generator} //= do {
		my $tg = $X->{TermGenerator}->new;
		$tg->set_stemmer(PublicInbox::Search::stemmer($self));
		$tg;
	}
}

sub index_phrase ($$$$) {
	my ($self, $text, $wdf_inc, $prefix) = @_;

	term_generator($self)->index_text($text, $wdf_inc, $prefix);
	$self->{term_generator}->increase_termpos;
}

sub index_phrase1 { # called by various ->index_extra
	my ($self, $pfx, $text) = @_;
	index_phrase $self, $text, 1, $pfx;
}

sub index_text1 { # called by various ->index_extra
	my ($self, $pfx, $text) = @_;
	$self->{term_generator}->index_text_without_positions($text, 1, $pfx);
}

sub add_bool_term ($$) {
	my ($doc, $pfx_term) = @_;
	if (length($pfx_term) > MAX_TERM_SIZE) {
		warn "W: skipping term: `$pfx_term'.length > ",
			MAX_TERM_SIZE, "\n";
	} else {
		$doc->add_boolean_term($pfx_term);
	}
}

sub index_boolean_term { # called by various ->index_extra
	my ($self, $pfx, $term) = @_;
	add_bool_term($self->{term_generator}->get_document, $pfx.$term);
}

sub index_text ($$$$) {
	my ($self, $text, $wdf_inc, $prefix) = @_;

	if ($self->{indexlevel} eq 'full') {
		index_phrase($self, $text, $wdf_inc, $prefix);
	} else {
		term_generator($self)->index_text_without_positions(
					$text, $wdf_inc, $prefix);
	}
}

sub index_headers ($$) {
	my ($self, $smsg) = @_;
	my @x = (from => 'A', to => 'XTO', cc => 'XCC'); # A: Author
	while (my ($field, $pfx) = splice(@x, 0, 2)) {
		my $val = $smsg->{$field};
		next if $val eq '';
		# include "(comments)" after the address, too, so not using
		# PublicInbox::Address::names or pairs
		index_text($self, $val, 1, $pfx);

		# we need positional info for email addresses since they
		# can be considered phrases
		if ($self->{indexlevel} eq 'medium') {
			for my $addr (PublicInbox::Address::emails($val)) {
				index_phrase($self, $addr, 1, $pfx);
			}
		}
	}
	@x = (subject => 'S');
	while (my ($field, $pfx) = splice(@x, 0, 2)) {
		my $val = $smsg->{$field};
		index_text($self, $val, 1, $pfx) if $val ne '';
	}
}

sub index_diff_inc ($$$$) {
	my ($self, $text, $pfx, $xnq) = @_;
	if (@$xnq) {
		index_text($self, join("\n", @$xnq), 1, 'XNQ');
		@$xnq = ();
	}
	if ($pfx eq 'XDFN') {
		index_phrase($self, $text, 1, $pfx);
	} else {
		index_text($self, $text, 1, $pfx);
	}
}

sub index_old_diff_fn {
	my ($self, $seen, $fa, $fb, $xnq) = @_;

	# no renames or space support for traditional diffs,
	# find the number of leading common paths to strip:
	my @fa = split(m'/', $fa);
	my @fb = split(m'/', $fb);
	while (scalar(@fa) && scalar(@fb)) {
		$fa = join('/', @fa);
		$fb = join('/', @fb);
		if ($fa eq $fb) {
			unless ($seen->{$fa}++) {
				index_diff_inc($self, $fa, 'XDFN', $xnq);
			}
			return 1;
		}
		shift @fa;
		shift @fb;
	}
	0;
}

sub index_diff ($$$) {
	my ($self, $txt, $doc) = @_;
	my %seen;
	my $in_diff;
	my $xnq = [];
	my @l = split(/\n/, $$txt);
	undef $$txt;
	while (defined($_ = shift @l)) {
		if ($in_diff && /^GIT binary patch/) {
			push @$xnq, $_;
			while (@l && $l[0] =~ /^(?:literal|delta) /) {
				# TODO allow searching by size range?
				# allows searching by exact size via:
				# "literal $SIZE" or "delta $SIZE"
				push @$xnq, shift(@l);

				# skip base85 and empty lines
				while (@l && ($l[0] =~ /\A$BASE85\s*\z/o ||
						$l[0] !~ /\S/)) {
					shift @l;
				}
				# loop hits trailing "literal 0\nHcmV?d00001\n"
			}
		} elsif ($in_diff && s/^ //) { # diff context
			index_diff_inc($self, $_, 'XDFCTX', $xnq);
		} elsif (/^-- $/) { # email signature begins
			$in_diff = undef;
		} elsif (m!^diff --git ("?[^/]+/.+) ("?[^/]+/.+)\z!) {
			# capture filenames here for binary diffs:
			my ($fa, $fb) = ($1, $2);
			push @$xnq, $_;
			$in_diff = 1;
			$fa = (split(m'/', git_unquote($fa), 2))[1];
			$fb = (split(m'/', git_unquote($fb), 2))[1];
			$seen{$fa}++ or index_diff_inc($self, $fa, 'XDFN', $xnq);
			$seen{$fb}++ or index_diff_inc($self, $fb, 'XDFN', $xnq);
		# traditional diff:
		} elsif (m/^diff -(.+) (\S+) (\S+)$/) {
			my ($opt, $fa, $fb) = ($1, $2, $3);
			push @$xnq, $_;
			# only support unified:
			next unless $opt =~ /[uU]/;
			$in_diff = index_old_diff_fn($self, \%seen, $fa, $fb,
							$xnq);
		} elsif (m!^--- ("?[^/]+/.+)!) {
			my $fn = $1;
			$fn = (split(m'/', git_unquote($fn), 2))[1];
			$seen{$fn}++ or index_diff_inc($self, $fn, 'XDFN', $xnq);
			$in_diff = 1;
		} elsif (m!^\+\+\+ ("?[^/]+/.+)!)  {
			my $fn = $1;
			$fn = (split(m'/', git_unquote($fn), 2))[1];
			$seen{$fn}++ or index_diff_inc($self, $fn, 'XDFN', $xnq);
			$in_diff = 1;
		} elsif (/^--- (\S+)/) {
			$in_diff = $1; # old diff filename
			push @$xnq, $_;
		} elsif (defined $in_diff && /^\+\+\+ (\S+)/) {
			$in_diff = index_old_diff_fn($self, \%seen, $in_diff,
							$1, $xnq);
		} elsif ($in_diff && s/^\+//) { # diff added
			index_diff_inc($self, $_, 'XDFB', $xnq);
		} elsif ($in_diff && s/^-//) { # diff removed
			index_diff_inc($self, $_, 'XDFA', $xnq);
		} elsif (m!^index ([a-f0-9]+)\.\.([a-f0-9]+)!) {
			my ($ba, $bb) = ($1, $2);
			index_git_blob_id($doc, 'XDFPRE', $ba);
			index_git_blob_id($doc, 'XDFPOST', $bb);
			$in_diff = 1;
		} elsif (/^@@ (?:\S+) (?:\S+) @@\s*$/) {
			# traditional diff w/o -p
		} elsif (/^@@ (?:\S+) (?:\S+) @@\s*(\S+.*)$/) {
			# hunk header context
			index_diff_inc($self, $1, 'XDFHH', $xnq);
		# ignore the following lines:
		} elsif (/^(?:dis)similarity index/ ||
				/^(?:old|new) mode/ ||
				/^(?:deleted|new) file mode/ ||
				/^(?:copy|rename) (?:from|to) / ||
				/^(?:dis)?similarity index / ||
				/^\\ No newline at end of file/ ||
				/^Binary files .* differ/) {
			push @$xnq, $_;
		} elsif ($_ eq '') {
			# possible to be in diff context, some mail may be
			# stripped by MUA or even GNU diff(1).  "git apply"
			# treats a bare "\n" as diff context, too
		} else {
			push @$xnq, $_;
			warn "non-diff line: $_\n" if DEBUG && $_ ne '';
			$in_diff = undef;
		}
	}

	index_text($self, join("\n", @$xnq), 1, 'XNQ');
}

sub index_body_text {
	my ($self, $doc, $sref) = @_;
	my $rd;
	# start patch-id in parallel
	if ($$sref =~ /^(?:diff|---|\+\+\+) /ms && !$PATCHID_BROKEN) {
		my $git = ($self->{ibx} // $self->{eidx} // $self)->git;
		my $fh = PublicInbox::IO::write_file '+>:utf8', undef, $$sref;
		$fh->flush or die "$fh->flush: $!";
		sysseek($fh, 0, SEEK_SET);
		$rd = popen_rd($git->cmd(qw(patch-id --stable)), undef,
				{ 0 => $fh });
	}

	# split off quoted and unquoted blocks:
	my @sections = PublicInbox::MsgIter::split_quotes($$sref);
	undef $$sref; # free memory
	for my $txt (@sections) {
		if ($txt =~ /\A>/) {
			if ($txt =~ /^[>\t ]+GIT binary patch\r?/sm) {
				# get rid of Base-85 noise
				$txt =~ s/^([>\h]+(?:literal|delta)
						\x20[0-9]+\h*\r*\n)
					(?:[>\h]+$BASE85\h*\r*\n)+/$1/gsmx;
			}
			index_text($self, $txt, 0, 'XQUOT');
		} else { # does it look like a diff?
			if ($txt =~ /^(?:diff|---|\+\+\+) /ms) {
				index_diff($self, \$txt, $doc);
			} else {
				index_text($self, $txt, 1, 'XNQ');
			}
		}
		undef $txt; # free memory
	}
	if (defined $rd) { # reap `git patch-id'
		(readline($rd) // '') =~ /\A([a-f0-9]{40,})/ and
			$doc->add_term('XDFID'.$1);
		if (!$rd->close) {
			my $c = 'git patch-id --stable';
			$PATCHID_BROKEN = ($? >> 8) == 129;
			$PATCHID_BROKEN ? warn("W: $c requires git v2.1.0+\n")
				: warn("W: $c failed: \$?=$? (non-fatal)");
		}
	}
}

sub index_xapian { # msg_iter callback
	my $part = $_[0]->[0]; # ignore $depth and $idx
	my ($self, $doc) = @{$_[1]};
	my $ct = $part->content_type || 'text/plain';
	my $fn = $part->filename;
	if (defined $fn && $fn ne '') {
		index_phrase($self, $fn, 1, 'XFN');
	}
	if ($part->{is_submsg}) {
		my $mids = mids_for_index($part);
		index_ids($self, $doc, $part, $mids);
		my $smsg = bless {}, 'PublicInbox::Smsg';
		$smsg->populate($part);
		index_headers($self, $smsg);
	}

	my ($s, undef) = msg_part_text($part, $ct);
	defined $s or return;
	$_[0]->[0] = $part = undef; # free memory
	index_body_text($self, $doc, \$s);
}

sub index_list_id_raw ($$@) {
	my ($self, $doc, @list_ids) = @_;
	for my $l (@list_ids) {
		$l =~ /<([^>]+)>/ or next;
		my $lid = lc $1;
		$lid =~ tr/\n\t\r\0//d; # same rules as Message-ID
		add_bool_term $doc, 'G' . $lid;
		index_phrase $self, $lid, 1, 'XL'; # probabilistic
	}
}

sub index_list_id ($$$) {
	my ($self, $doc, $hdr) = @_;
	index_list_id_raw $self, $doc, $hdr->header_raw('List-Id');
}

sub index_ids ($$$$) {
	my ($self, $doc, $hdr, $mids) = @_;
	for my $mid (@$mids) {
		index_phrase($self, $mid, 1, 'XM');

		# because too many Message-IDs are prefixed with
		# "Pine.LNX."...
		if ($mid =~ /\w{12,}/) {
			my @long = ($mid =~ /(\w{3,}+)/g);
			index_phrase($self, join(' ', @long), 1, 'XM');
		}
	}
	add_bool_term($doc, 'Q'.$_) for @$mids;
	index_list_id $self, $doc, $hdr;
}

sub eml2doc ($$$;$) {
	my ($self, $eml, $smsg, $mids) = @_;
	$mids //= mids_for_index($eml);
	my $doc = $X->{Document}->new;
	add_val($doc, PublicInbox::Search::TS(), $smsg->{ts});
	my @ds = gmtime($smsg->{ds});
	my $yyyymmdd = strftime('%Y%m%d', @ds);
	add_val($doc, PublicInbox::Search::YYYYMMDD(), $yyyymmdd);
	my $dt = strftime('%Y%m%d%H%M%S', @ds);
	add_val($doc, PublicInbox::Search::DT(), $dt);
	add_val($doc, PublicInbox::Search::BYTES(), $smsg->{bytes});
	add_val($doc, PublicInbox::Search::UID(), $smsg->{num});
	add_val($doc, PublicInbox::Search::THREADID, $smsg->{tid});

	term_generator($self)->set_document($doc);
	index_headers($self, $smsg);

	my $ekey = $smsg->{eidx_key};
	add_bool_term($doc, 'O'.$ekey) if ($ekey // '.') ne '.';
	msg_iter($eml, \&index_xapian, [ $self, $doc ]);
	index_ids($self, $doc, $eml, $mids);
	for (@{$smsg->parse_references($eml, $mids)}) {
		add_bool_term $doc, 'XRF'.$_;
	}

	# by default, we maintain compatibility with v1.5.0 and earlier
	# by writing to docdata.glass, users who never expect to downgrade can
	# use --skip-docdata
	if (!$self->{-skip_docdata}) {
		# WWW doesn't need {to} or {cc}, only NNTP
		$smsg->{to} = $smsg->{cc} = '';
		$doc->set_data($smsg->to_doc_data);
	}
	my $xtra = defined $ekey ? $self->{"-extra\t$ekey"} : undef;
	$xtra //= $self->{-extra};
	for my $e (@$xtra) {
		$e->index_extra($self, $eml, $mids);
	}
	$doc;
}

sub _xdb_tmp_new ($$$) {
	my ($self, $dir, $flags) = @_;
	$flags |= $DB_DANGEROUS | $DB_NO_SYNC;
	my $xdb_tmp;
	eval {
		$xdb_tmp = xap_wdb $dir, $flags, $self->{-opt};
		$xdb_tmp->begin_transaction;
	};
	if (my $err = $@) { # rethrow for stacktrace w/ PERL5OPT=-MCarp=verbose
		my @offs = sort { $a <=> $b } keys %{$self->{-xdb_tmp}};
		croak $err, "E: xdb_tmps active: @offs";
	}
	$xdb_tmp;
}

sub xdb_tmp_new ($$$) {
	my ($self, $off, $docid) = @_;
	my $dir = $self->xdir.".$off.tmp";
	my $restore = $self->with_umask;
	if (mkdir $dir) {
		my $pr = $self->{-opt}->{-progress};
		$pr->("indexing >= #$docid to ",($self->{shard}//''),
			".$off.tmp...\n") if $pr;
		PublicInbox::Syscall::nodatacow_dir($dir);
	}
	$self->{-xdb_tmp}->{$off} = _xdb_tmp_new $self, $dir, $DB_CREATE_OR_OPEN
}

sub xdb_tmp_get ($$) {
	my ($self, $off) = @_;
	my $dir = $self->xdir.".$off.tmp";
	$self->{-xdb_tmp}->{$off} = _xdb_tmp_new $self, $dir, $DB_OPEN;
}

sub replace_doc ($$$) {
	my ($self, $docid, $doc) = @_;
	my ($xdb_tmp, $doc_max);
	if (($doc_max = $self->{-doc_max}) && $docid > $doc_max) {
		my $n = $self->{-opt}->{'split-at'} || $SHARD_SPLIT_AT;
		my $off = int($docid / $n);
		$xdb_tmp = $self->{-xdb_tmp}->{$off} //
					xdb_tmp_new $self, $off, $docid;
	}
	($xdb_tmp // $self->{xdb})->replace_document($docid, $doc);
}

sub _get_doc ($$) {
	my ($self, $docid) = @_;
	my ($xdb_tmp, $doc_max, $doc);
	if (($doc_max = $self->{-doc_max}) && $docid > $doc_max) {
		my $n = $self->{-opt}->{'split-at'} || $SHARD_SPLIT_AT;
		my $off = int($docid / $n);
		$xdb_tmp = $self->{-xdb_tmp}->{$off} // xdb_tmp_get $self, $off;
	}
	$doc = eval { ($xdb_tmp // $self->{xdb})->get_document($docid) };
	if ($@) {
		die $@ if ref($@) !~ /\bDocNotFoundError\b/;
		warn "E: #$docid missing in Xapian\n";
	}
	$doc;
}

sub add_xapian ($$$$) {
	my ($self, $eml, $smsg, $mids) = @_;
	begin_txn_lazy($self);
	my ($merge_vmd, $eidx_more) = delete @$smsg{qw(-merge_vmd -eidx_more)};
	my $doc = eml2doc($self, $eml, $smsg, $mids);
	if (my $old = $merge_vmd ? _get_doc($self, $smsg->{num}) : undef) {
		my @x = @VMD_MAP;
		while (my ($field, $pfx) = splice(@x, 0, 2)) {
			for my $term (xap_terms($pfx, $old)) {
				add_bool_term $doc, $pfx.$term;
			}
		}
	}
	for (@$eidx_more) {
		my ($eidx_key, @list_ids) = @$_;
		add_bool_term($doc, 'O'.$eidx_key) if $eidx_key ne '.';
		index_list_id_raw $self, $doc, @list_ids;
	}
	replace_doc $self, $smsg->{num}, $doc;
}

sub v1_mm_init ($) {
	my ($self) = @_;
	die "BUG: v1_mm_init is only for v1\n" if $self->{ibx}->version != 1;
	$self->{mm} //= do {
		require PublicInbox::Msgmap;
		PublicInbox::Msgmap->new_file($self->{ibx}, $self->{-opt});
	};
}

sub v1_index_mm ($$$) {
	my ($self, $eml, $oid) = @_;
	my $mids = mids($eml);
	my $mm = $self->{mm};
	if ($self->{reindex}) {
		my $oidx = $self->{oidx};
		for my $mid (@$mids) {
			my ($num, undef) = $oidx->num_mid0_for_oid($oid, $mid);
			return $num if defined $num;
		}
		$mm->num_for($mids->[0]) // $mm->mid_insert($mids->[0]);
	} else {
		# fallback to num_for since filters like RubyLang set the number
		$mm->mid_insert($mids->[0]) // $mm->num_for($mids->[0]);
	}
}

sub add_message { # v1 + tests only
	# mime = PublicInbox::Eml or Email::MIME object
	my ($self, $mime, $smsg, $cmt_info) = @_;
	begin_txn_lazy($self);
	my $mids = mids_for_index($mime);
	$smsg //= bless { blob => '' }, 'PublicInbox::Smsg'; # test-only compat
	$smsg->{mid} //= $mids->[0]; # v1 compatibility
	$smsg->{num} //= do { # v1
		v1_mm_init $self;
		v1_index_mm $self, $mime, $smsg->{blob};
	};

	# v1 and tests only:
	$smsg->populate($mime, $cmt_info);
	$smsg->{bytes} //= length($mime->as_string);

	eval {
		# order matters, overview stores every possible piece of
		# data in doc_data (deflated).  Xapian only stores a subset
		# of the fields which exist in over.sqlite3.  We may stop
		# storing doc_data in Xapian sometime after we get multi-inbox
		# search working.
		if (my $oidx = $self->{oidx}) { # v1 only
			$oidx->add_overview($mime, $smsg);
		}
		if (need_xapian($self)) {
			add_xapian($self, $mime, $smsg, $mids);
		}
	};

	if ($@) {
		warn "failed to index message <".join('> <',@$mids).">: $@\n";
		return undef;
	}
	$smsg->{num};
}

sub add_eidx_info_raw {
	my ($self, $docid, $eidx_key, @list_ids) = @_;
	begin_txn_lazy($self);
	my $doc = _get_doc($self, $docid) or return;
	term_generator($self)->set_document($doc);

	# '.' is special for lei_store
	add_bool_term($doc, 'O'.$eidx_key) if $eidx_key ne '.';

	index_list_id_raw $self, $doc, @list_ids;
	replace_doc $self, $docid, $doc;
}

# for lei/store to access uncommitted terms
sub get_terms {
	my ($self, $pfx, $docid) = @_;
	begin_txn_lazy($self);
	xap_terms($pfx, $self->{xdb}, $docid);
}

sub remove_eidx_info_raw {
	my ($self, $docid, $eidx_key, @list_ids) = @_;
	begin_txn_lazy($self);
	my $doc = _get_doc($self, $docid) or return;
	eval { $doc->remove_term('O'.$eidx_key) };
	warn "W: ->remove_term O$eidx_key: $@\n" if $@;
	for my $l (@list_ids) {
		$l =~ /<([^>]+)>/ or next;
		my $lid = lc $1;
		eval { $doc->remove_term('G' . $lid) };
		warn "W: ->remove_term G$lid: $@\n" if $@;

		# nb: we don't remove the XL probabilistic terms
		# since terms may overlap if cross-posted.
		#
		# IOW, a message which has both <foo.example.com>
		# and <bar.example.com> would have overlapping
		# "XLexample" and "XLcom" as terms and which we
		# wouldn't know if they're safe to remove if we just
		# unindex <foo.example.com> while preserving
		# <bar.example.com>.
		#
		# In any case, this entire sub is will likely never
		# be needed and users using the "l:" prefix are probably
		# rarer.
	}
	replace_doc $self, $docid, $doc;
}

sub set_vmd {
	my ($self, $docid, $vmd) = @_;
	begin_txn_lazy($self);
	my $doc = _get_doc($self, $docid) or return;
	my ($v, @rm, @add);
	my @x = @VMD_MAP;
	my ($cur, $end) = ($doc->termlist_begin, $doc->termlist_end);
	while (my ($field, $pfx) = splice(@x, 0, 2)) {
		my $set = $vmd->{$field} // next;
		my %keep = map { $_ => 1 } @$set;
		my %add = %keep;
		$cur->skip_to($pfx); # works due to @VMD_MAP order
		for (; $cur != $end; $cur++) {
			$v = $cur->get_termname;
			$v =~ s/\A$pfx//s or next;
			$keep{$v} ? delete($add{$v}) : push(@rm, $pfx.$v);
		}
		push(@add, map { $pfx.$_ } keys %add);
	}
	return unless scalar(@rm) || scalar(@add);
	$doc->remove_term($_) for @rm;
	add_bool_term($doc, $_) for @add;
	replace_doc $self, $docid, $doc;
}

sub apply_vmd_mod ($$) {
	my ($doc, $vmd_mod) = @_;
	my $updated = 0;
	my @x = @VMD_MAP;
	while (my ($field, $pfx) = splice(@x, 0, 2)) {
		# field: "L" or "kw"
		for my $val (@{$vmd_mod->{"-$field"} // []}) {
			eval {
				$doc->remove_term($pfx . $val);
				++$updated;
			};
		}
		for my $val (@{$vmd_mod->{"+$field"} // []}) {
			add_bool_term($doc, $pfx . $val);
			++$updated;
		}
	}
	$updated;
}

sub add_vmd {
	my ($self, $docid, $vmd) = @_;
	begin_txn_lazy($self);
	my $doc = _get_doc($self, $docid) or return;
	my @x = @VMD_MAP;
	my $updated = 0;
	while (my ($field, $pfx) = splice(@x, 0, 2)) {
		my $add = $vmd->{$field} // next;
		add_bool_term($doc, $pfx . $_) for @$add;
		$updated += scalar(@$add);
	}
	$updated += apply_vmd_mod($doc, $vmd);
	replace_doc($self, $docid, $doc) if $updated;
}

sub remove_vmd {
	my ($self, $docid, $vmd) = @_;
	begin_txn_lazy($self);
	my $doc = _get_doc($self, $docid) or return;
	my $replace;
	my @x = @VMD_MAP;
	while (my ($field, $pfx) = splice(@x, 0, 2)) {
		my $rm = $vmd->{$field} // next;
		for (@$rm) {
			eval {
				$doc->remove_term($pfx . $_);
				$replace = 1;
			};
		}
	}
	replace_doc($self, $docid, $doc) if $replace;
}

sub update_vmd {
	my ($self, $docid, $vmd_mod) = @_;
	begin_txn_lazy($self);
	my $doc = _get_doc($self, $docid) or return;
	my $updated = apply_vmd_mod($doc, $vmd_mod);
	replace_doc($self, $docid, $doc) if $updated;
	$updated;
}

sub _xdb_remove ($@) {
	my ($self, @docids) = @_;
	my @warn;
	begin_txn_lazy($self);
	my $xdb = $self->{xdb} // die 'BUG: missing {xdb}';
	if (my $doc_max = $self->{-doc_max}) {
		my $n = $self->{-opt}->{'split-at'} || $SHARD_SPLIT_AT;
		for my $docid (grep { $_ > $doc_max } @docids) {
			my $off = int($docid / $n);
			my $xdb_tmp = $self->{-xdb_tmp}->{$off} //
							xdb_tmp_get $self, $off;
			eval { $xdb_tmp->delete_document($docid) };
			push(@warn, "E: #$docid not in Xapian tmp[$off]? $@\n")
				if $@;
		}
		@docids = grep { $_ <= $doc_max } @docids;
	}
	for my $docid (@docids) {
		eval { $xdb->delete_document($docid) };
		push(@warn, "E: #$docid not in Xapian? $@\n") if $@;
	}
	@warn;
}

sub xdb_remove {
	my ($self, @docids) = @_;
	my @warn = _xdb_remove $self, @docids;
	warn @warn if @warn;
}

sub xdb_remove_quiet {
	my ($self, @docids) = @_;
	my @warn = _xdb_remove $self, @docids;
	$self->{-quiet_rm} += (scalar(@docids) - scalar(@warn));
}

sub nr_quiet_rm { delete($_[0]->{-quiet_rm}) // 0 }

sub index_git_blob_id {
	my ($doc, $pfx, $objid) = @_;

	for (my $len = length($objid); $len >= 7; ) {
		$doc->add_term($pfx.$objid);
		$objid = substr($objid, 0, --$len);
	}
}

sub v1_unindex_eml ($$$) {
	my ($self, $oid, $eml) = @_;
	my $mids = mids($eml);
	my $nr = 0;
	my %tmp;
	for my $mid (@$mids) {
		my @removed = $self->{oidx}->remove_oid($oid, $mid);
		$nr += scalar @removed;
		$tmp{$_}++ for @removed;
	}
	if (!$nr) {
		my $m = join('> <', @$mids);
		warn "W: <$m> missing for removal from overview\n";
	}
	while (my ($num, $nr) = each %tmp) {
		warn "BUG: $num appears >1 times ($nr) for $oid\n" if $nr != 1;
	}
	if ($nr) {
		$self->{mm}->num_delete($_) for (keys %tmp);
	} else { # just in case msgmap and over.sqlite3 become desynched:
		$self->{mm}->mid_delete($mids->[0]);
	}
	xdb_remove($self, keys %tmp) if need_xapian($self);
}

sub is_bad_blob ($$$$) {
	my ($oid, $type, $size, $expect_oid) = @_;
	if ($type ne 'blob') {
		carp "W: $expect_oid is not a blob (type=$type)";
		return 1;
	}
	croak "BUG: $oid != $expect_oid" if $oid ne $expect_oid;
	$size == 0 ? 1 : 0; # size == 0 means purged
}

# returns true if checkpoint is needed
sub update_checkpoint ($;$) {
	my ($self, $bytes) = @_;
	my $nr = $self->{transact_bytes} += $bytes // 0;
	$self->{need_checkpoint} // return; # must be defined via local
	return ++$self->{need_checkpoint} if $nr >= $self->{batch_bytes};
	my $now = now;
	my $next = $self->{next_checkpoint} //= $now +
		($self->{-opt}->{'commit-interval'} // $CHECKPOINT_INTVL);
	$self->{need_checkpoint} += ($now > $next ? 1 : 0);
}

sub v1_index_both { # git->cat_async callback
	my ($bref, $oid, $type, $size, $arg) = @_;
	return if is_bad_blob($oid, $type, $size, $arg->{oid});
	my $smsg = bless { blob => $oid }, 'PublicInbox::Smsg';
	$smsg->set_bytes($$bref, $size);
	my $self = $arg->{self};
	update_checkpoint $self, $smsg->{bytes};
	local $self->{current_info} = "$self->{current_info}: $oid";
	my $eml = PublicInbox::Eml->new($bref);
	$smsg->{num} = v1_index_mm $self, $eml, $oid or
		die "E: could not generate NNTP article number for $oid";
	add_message($self, $eml, $smsg, $arg);
	++$self->{nidx};
	++$self->{nrec};
	my $cur_cmt = $arg->{cur_cmt} // die 'BUG: {cur_cmt} missing';
	$self->{latest_cmt} = $cur_cmt;
}

sub v1_unindex_both { # git->cat_async callback
	my ($bref, $oid, $type, $size, $arg) = @_;
	return if is_bad_blob($oid, $type, $size, $arg->{oid});
	my $self = $arg->{self};
	local $self->{current_info} = "$self->{current_info}: $oid";
	v1_unindex_eml $self, $oid, PublicInbox::Eml->new($bref);
	# may be undef if leftover
	if (defined(my $cur_cmt = $arg->{cur_cmt})) {
		$self->{latest_cmt} = $cur_cmt;
	}
	++$self->{nidx};
}

sub with_umask {
	my $self = shift;
	my $owner = $self->{ibx} // $self->{eidx};
	$owner ? $owner->with_umask(@_) : $self->SUPER::with_umask(@_)
}

# called by public-inbox-index
sub index_sync {
	my ($self, $opt) = @_;
	delete $self->{lock_path} if $opt->{-skip_lock};
	$self->with_umask(\&_index_sync, $self, $opt);
	if ($opt->{reindex} && !$self->{quit} &&
			!grep(defined, @$opt{qw(since until)})) {
		my %again = %$opt;
		delete @again{qw(rethread reindex)};
		index_sync($self, \%again);
	}
}

sub check_size { # check_async cb for -index --max-size=...
	my (undef, $oid, $type, $size, $arg) = @_;
	my $self = $arg->{self};
	($type // '') eq 'blob' or
		die "E: bad $oid in $self->{ibx}->{git}->{git_dir}";
	if ($size <= $self->{max_size}) {
		$self->{ibx}->{git}->cat_async($oid, $self->{index_oid}, $arg);
	} else {
		warn "W: skipping $oid ($size > $self->{max_size})\n";
	}
}

sub v1_checkpoint ($;$) {
	my ($self, $stk) = @_;
	$self->{ibx}->git->async_wait_all;
	$self->{need_checkpoint} = 0;

	# $newest may be undef
	my $newest = $stk ? $stk->{latest_cmt} : $self->{latest_cmt};
	if (defined($newest)) {
		my $cur = $self->{mm}->last_commit;
		if (v1_need_update($self, $cur, $newest)) {
			$self->{mm}->last_commit($newest);
		}
	}
	$self->{mm}->mm_commit;
	my $xdb = $self->{xdb};
	if ($newest && $xdb) {
		my $cur = $xdb->get_metadata('last_commit');
		if (v1_need_update($self, $cur, $newest)) {
			$xdb->set_metadata('last_commit', $newest);
		}
	}
	if ($stk) { # all done if $stk is passed
		# let SearchView know a full --reindex was done so it can
		# generate ->has_threadid-dependent links
		if ($xdb && $self->{reindex} && !ref($self->{reindex})) {
			my $n = $xdb->get_metadata('has_threadid');
			$xdb->set_metadata('has_threadid', '1') if $n ne '1';
		}
		$self->{oidx}->rethread_done($self->{-opt}); # all done
	}
	commit_txn_lazy($self);
	$self->{ibx}->git->cleanup;
	my $nrec = $self->{nrec};
	idx_release($self, $nrec);
	# let another process do some work...
	if (my $pr = $self->{-opt}->{-progress}) {
		$pr->("indexed $nrec/$self->{ntodo}\n") if $nrec;
	}
	if (!$stk && !$self->{quit}) { # more to come
		begin_txn_lazy($self);
		$self->{mm}->{dbh}->begin_work;
	}
	$self->{transact_bytes} = 0;
	delete $self->{next_checkpoint};
}

sub v1_process_stack ($$) {
	my ($self, $stk) = @_;
	my $git = $self->{ibx}->git;
	$self->{nrec} = 0;
	local $self->{need_checkpoint} = 0;
	local $self->{latest_cmt};

	$self->{mm}->{dbh}->begin_work;
	if (my @leftovers = keys %{delete($self->{D}) // {}}) {
		warn('W: unindexing '.scalar(@leftovers)." leftovers\n");
		for my $oid (@leftovers) {
			last if $self->{quit};
			$oid = unpack('H*', $oid);
			my $arg = { oid => $oid, self => $self };
			$git->cat_async($oid, \&v1_unindex_both, $arg);
		}
	}
	$self->{max_size} = $self->{-opt}->{max_size} and
		$self->{index_oid} = \&v1_index_both;
	while (my ($f, $at, $ct, $oid, $cur_cmt) = $stk->pop_rec) {
		my $arg = { self => $self, cur_cmt => $cur_cmt, oid => $oid };
		last if $self->{quit};
		if ($f eq 'm') {
			$arg->{autime} = $at;
			$arg->{cotime} = $ct;
			if ($self->{max_size}) {
				$git->check_async($oid, \&check_size, $arg);
			} else {
				$git->cat_async($oid, \&v1_index_both, $arg);
			}
		} elsif ($f eq 'd') {
			$git->cat_async($oid, \&v1_unindex_both, $arg);
		}
		v1_checkpoint $self if $self->{need_checkpoint};
	}
	v1_checkpoint($self, $self->{quit} ? undef : $stk);
}

sub log2stack ($$$) {
	my ($self, $git, $range) = @_;
	my $D = $self->{D}; # OID_BIN => NR (if reindexing, undef otherwise)
	my ($add, $del);
	if ($self->{ibx}->version == 1) {
		my $path = $hex.'{2}/'.$hex.'{38}';
		$add = qr!\A:000000 100644 \S+ ($OID) A\t$path$!;
		$del = qr!\A:100644 000000 ($OID) \S+ D\t$path$!;
	} else {
		$del = qr!\A:\d{6} 100644 $OID ($OID) [AM]\td$!;
		$add = qr!\A:\d{6} 100644 $OID ($OID) [AM]\tm$!;
	}

	# Count the new files so they can be added newest to oldest
	# and still have numbers increasing from oldest to newest
	my @cmd = qw(log --raw -r --pretty=tformat:%at-%ct-%H
			--no-notes --no-color --no-renames --no-abbrev);
	for my $k (qw(since until)) {
		my $v = $self->{-opt}->{$k} // next;
		next if !$self->{-opt}->{reindex};
		push @cmd, "--$k=$v";
	}
	my $fh = $git->popen(@cmd, $range);
	my ($at, $ct, $stk, $cmt, $l);
	while (defined($l = <$fh>)) {
		return if $self->{quit};
		if ($l =~ /\A([0-9]+)-([0-9]+)-($OID)$/o) {
			($at, $ct, $cmt) = ($1 + 0, $2 + 0, $3);
			$stk //= PublicInbox::IdxStack->new($cmt);
		} elsif ($l =~ /$del/) {
			my $oid = $1;
			if ($D) { # reindex case
				$D->{pack('H*', $oid)}++;
			} else { # non-reindex case:
				$stk->push_rec('d', $at, $ct, $oid, $cmt);
			}
		} elsif ($l =~ /$add/) {
			my $oid = $1;
			if ($D) {
				my $oid_bin = pack('H*', $oid);
				my $nr = --$D->{$oid_bin};
				delete($D->{$oid_bin}) if $nr <= 0;
				# nr < 0 (-1) means it never existed
				next if $nr >= 0;
			}
			$stk->push_rec('m', $at, $ct, $oid, $cmt);
		}
	}
	$fh->close or die "git log failed: \$?=$?";
	$stk //= PublicInbox::IdxStack->new;
	$stk->read_prepare;
}

sub prepare_stack ($$) {
	my ($self, $range) = @_;
	my $git = $self->{ibx}->git;

	if (index($range, '..') < 0) {
		# don't show annoying git errors to users who run -index
		# on empty inboxes
		$git->qx(qw(rev-parse -q --verify), "$range^0");
		return PublicInbox::IdxStack->new->read_prepare if $?;
	}
	local $self->{D} = $self->{reindex} ? {} : undef; # OID_BIN => NR
	log2stack $self, $git, $range;
}

# --is-ancestor requires git 1.8.0+
sub is_ancestor ($$$) {
	my ($git, $cur, $tip) = @_;
	return 0 unless $git->check($cur);
	my $cmd = $git->cmd(qw(merge-base --is-ancestor), $cur, $tip);
	run_wait($cmd) == 0;
}

sub v1_need_update ($$$) {
	my ($self, $cur, $new) = @_;
	my $git = $self->{ibx}->git;
	$cur //= ''; # XS Search::Xapian ->get_metadata doesn't give undef

	# don't rewind if --{since,until,before,after} are in use
	return if $cur ne '' &&
		grep(defined, @{$self->{-opt}}{qw(since until)}) &&
		is_ancestor($git, $new, $cur);

	return 1 if $cur ne '' && !is_ancestor($git, $cur, $new);
	my $range = $cur eq '' ? $new : "$cur..$new";
	chomp(my $n = $git->qx(qw(rev-list --count), $range));
	($n eq '' || $n > 0);
}

# The last git commit we indexed with Xapian or SQLite (msgmap)
# This needs to account for cases where Xapian or SQLite is
# out-of-date with respect to the other.
sub v1_last_x_commit ($$) {
	my ($self, $mm) = @_;
	my $lm = $mm->last_commit || '';
	my $lx = '';
	if (need_xapian($self)) {
		$lx = $self->{xdb}->get_metadata('last_commit') || '';
	} else {
		$lx = $lm;
	}
	# Use last_commit from msgmap if it is older or unset
	if (!$lm || ($lx && $lm && is_ancestor($self->{ibx}->git, $lm, $lx))) {
		$lx = $lm;
	}
	$lx;
}

sub v1_reindex_from ($$) {
	my ($reindex, $last_commit) = @_;
	return $last_commit unless $reindex;
	ref($reindex) eq 'HASH' ? $reindex->{from} : '';
}

sub quit_cb ($) {
	my ($self) = @_;
	sub {
		# we set {-opt}->{quit} for public-inbox-index so
		# can abort multi-inbox loops this way (for now...)
		$self->{quit} = $self->{-opt}->{quit} = 1;
		warn "# gracefully quitting\n";
	}
}

# indexes all unindexed messages (v1 only)
sub _index_sync {
	my ($self, $opt) = @_;
	my $tip = $opt->{ref} || 'HEAD';
	my $ibx = $self->{ibx};
	local $self->{current_info} = "$ibx->{inboxdir}";
	$self->{batch_bytes} = $opt->{batch_size} // $BATCH_BYTES;

	if ($X->{CLOEXEC_UNSET}) {
		$ibx->git->cat_file($tip);
		$ibx->git->check($tip);
	}
	local $self->{transact_bytes} = 0;
	my $pr = $opt->{-progress};
	local $self->{-opt} = $opt;
	local $self->{reindex} = $opt->{reindex};
	my $quit = quit_cb $self;
	local $SIG{QUIT} = $quit;
	local $SIG{INT} = $quit;
	local $SIG{TERM} = $quit;
	my $xdb = $self->begin_txn_lazy;
	$self->{oidx}->rethread_prepare($opt);
	my $mm = v1_mm_init $self;
	if ($self->{reindex}) {
		my $last = $mm->last_commit;
		if ($last) {
			$tip = $last;
		} else {
			# somebody just blindly added --reindex when indexing
			# for the first time, allow it:
			delete $self->{reindex};
		}
	}
	my $last_commit = v1_last_x_commit $self, $mm;
	my $lx = v1_reindex_from $self->{reindex}, $last_commit;
	my $range = $lx eq '' ? $tip : "$lx..$tip";
	$pr->("counting changes\n\t$range ... ") if $pr;
	my $stk = prepare_stack $self, $range;
	local $self->{ntodo} = $stk ? $stk->num_records : 0;
	$pr->("$self->{ntodo}\n") if $pr; # continue previous line
	v1_process_stack($self, $stk) if !$self->{quit};
}

sub DESTROY {
	# order matters for unlocking
	$_[0]->{xdb} = undef;
	delete $_[0]->{-xdb_tmp};
	$_[0]->{lockfh} = undef;
}

sub begin_txn_lazy {
	my ($self) = @_;
	return if $self->{txn};
	my $restore = $self->with_umask;
	my $xdb = $self->{xdb} || idx_acquire($self);
	$self->{oidx}->begin_lazy if $self->{oidx};
	$xdb->begin_transaction if $xdb;
	$self->{txn} = 1;
	$xdb;
}

# store 'indexlevel=medium' in v2 shard=0 and v1 (only one shard)
# This metadata is read by InboxWritable->detect_indexlevel:
sub set_metadata_once {
	my ($self) = @_;

	return if $self->{shard}; # only continue if undef or 0, not >0
	my $xdb = $self->{xdb};

	if (delete($self->{-set_has_threadid_once})) {
		$xdb->set_metadata('has_threadid', '1');
	}
	if (delete($self->{-set_indexlevel_once})) {
		my $level = $xdb->get_metadata('indexlevel');
		if (!$level || $level ne 'medium') {
			$xdb->set_metadata('indexlevel', 'medium');
		}
	}
	if (delete($self->{-set_skip_docdata_once})) {
		$xdb->get_metadata('skip_docdata') or
			$xdb->set_metadata('skip_docdata', '1');
	}
}

sub commit_txn_lazy {
	my ($self) = @_;
	return unless delete($self->{txn});
	my $restore = $self->with_umask;
	if (my $eidx = $self->{eidx}) {
		$eidx->git->async_wait_all;
		$eidx->{transact_bytes} = 0;
	}
	if (my $xdb = $self->{xdb}) {
		set_metadata_once($self);
		$xdb->commit_transaction;
	}
	# for memory savings:
	for my $xdb_tmp (values %{delete $self->{-xdb_tmp} // {}}) {
		$xdb_tmp->commit_transaction;
		$xdb_tmp->close; # I wasted a day because I forgot this line :<
		$self->{-splits_dirty} = 1;
	}
	$self->{oidx}->commit_lazy if $self->{oidx}; # v1 only
}

sub eidx_shard_new {
	my ($class, $eidx, $shard) = @_;
	my $self = bless {
		eidx => $eidx,
		-opt => $eidx->{-opt}, # hmm...
		xpfx => $eidx->{xpfx},
		indexlevel => $eidx->{indexlevel},
		-skip_docdata => 1,
		shard => $shard,
		creat => 1,
	}, $class;
	$self->{-set_indexlevel_once} = 1 if $self->{indexlevel} eq 'medium';
	$self->load_extra_indexers($eidx);
	require PublicInbox::Isearch;
	my $all = $self->{-extra};
	for my $ibx (@{$eidx->{ibx_active} // []}) {
		my $isrch = PublicInbox::Isearch->new($ibx);
		my $per_ibx = $isrch->{-extra} // next;
		$self->{"-extra\t$isrch->{eidx_key}"} =
					$all ? [ @$per_ibx, @$all ] : $per_ibx;
	}
	$self;
}

# calculate the next article number to defrag at
sub next_defrag ($$) {
	my ($num, $opt) = @_;
	my $nr = ($opt->{defrag} // $DEFRAG_NR) || return;
	$num ||= 1; # num == 0 on new DB
	$num + $nr - ($num % $nr);
}

sub defrag_xdir {
	my ($self) = @_;
	# e.g. xap15/[0123]/*.{glass,honey}, skip flintlock+iam{glass,*}
	for (glob($self->xdir.'/*.*')) {
		next if /\.sqlite3/; # v1 has over.sqlite3*
		last unless defrag_file $_
	}
}

1;
