# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# Combine any combination of PublicInbox::Search,
# PublicInbox::ExtSearch, and PublicInbox::LeiSearch objects
# into one Xapian DB
package PublicInbox::LeiXSearch;
use strict;
use v5.10.1;
use parent qw(PublicInbox::LeiSearch PublicInbox::IPC);
use PublicInbox::DS qw(now);
use File::Temp 0.19 (); # 0.19 for ->newdir
use File::Spec ();
use PublicInbox::Search qw(xap_terms);
use PublicInbox::Spawn qw(popen_rd popen_wr which);
use PublicInbox::MID qw(mids mid_escape);
use PublicInbox::Smsg;
use PublicInbox::Eml;
use PublicInbox::LEI;
use Fcntl qw(SEEK_SET F_SETFL O_APPEND O_RDWR);
use PublicInbox::ContentHash qw(git_sha);
use POSIX qw(strftime);
use autodie qw(close open pipe read seek truncate);
use PublicInbox::Syscall qw($F_SETPIPE_SZ);
use PublicInbox::OnDestroy;

sub new {
	my ($class) = @_;
	PublicInbox::Search::load_xapian();
	bless {
		qp_flags => $PublicInbox::Search::QP_FLAGS |
				PublicInbox::Search::FLAG_PURE_NOT(),
	}, $class
}

sub attach_external {
	my ($self, $ibxish) = @_; # ibxish = ExtSearch or Inbox
	my $desc = $ibxish->{inboxdir} // $ibxish->{topdir};
	my $srch = $ibxish->search //
		return warn("$desc not indexed for Xapian ($@ $!)\n");
	my @shards = $srch->xdb_shards_flat or
		return warn("$desc has no Xapian shards\n");
	my @dirs = $srch->shard_dirs or
		return warn("$desc has no Xapian shard dirs\n");

	if (delete $self->{xdb}) { # XXX: do we need this?
		# clobber existing {xdb} if amending
		my $expect = delete $self->{nshard};
		my $shards = delete $self->{shards_flat};
		scalar(@$shards) == $expect or die
			"BUG: {nshard}$expect != shards=".scalar(@$shards);

		my $prev = {};
		for my $old_ibxish (@{$self->{shard2ibx}}) {
			next if $prev == $old_ibxish;
			$prev = $old_ibxish;
			my @shards = $old_ibxish->search->xdb_shards_flat;
			push @{$self->{shards_flat}}, @shards;
		}
		my $nr = scalar(@{$self->{shards_flat}});
		$nr == $expect or die
			"BUG: reloaded $nr shards, expected $expect"
	}
	push @{$self->{shards_flat}}, @shards;
	push @{$self->{shard_dirs}}, @dirs;
	push @{$self->{open_locks}}, $srch->open_lock;
	push(@{$self->{shard2ibx}}, $ibxish) for (@shards);
}

sub shard_dirs { @{$_[0]->{shard_dirs}} }

sub xh_lock_args { map { ('-l', $_) } @{$_[0]->{open_locks}} }

# returns a list of local inboxes (or count in scalar context)
sub locals { @{$_[0]->{locals} // []} }

sub remotes { @{$_[0]->{remotes} // []} }

# called by PublicInbox::Search::xdb (usually via ->mset)
sub xdb_shards_flat { @{$_[0]->{shards_flat} // []} }

sub _mitem_kw { # retry_reopen callback
	my ($srch, $smsg, $mitem, $flagged) = @_;
	my $doc = $srch->{xdb}->get_document($mitem->get_docid);
	my $kw = xap_terms('K', $doc);
	$kw->{flagged} = 1 if $flagged;
	my @L = xap_terms('L', $doc);
	# we keep the empty {kw} array here to prevent expensive work in
	# ->xsmsg_vmd, _unbless_smsg will clobber it iff it's empty
	$smsg->{kw} = [ sort keys %$kw ];
	$smsg->{L} = \@L if scalar(@L);
}

sub mitem_kw ($$$;$) {
	my ($srch, $smsg, $mitem, $flagged) = @_;
	$srch->retry_reopen(\&_mitem_kw, $smsg, $mitem, $flagged);
}

# like over->get_art
sub smsg_for {
	my ($self, $mitem) = @_;
	# cf. https://trac.xapian.org/wiki/FAQ/MultiDatabaseDocumentID
	my $nshard = $self->{nshard};
	my $docid = $mitem->get_docid;
	my $shard = ($docid - 1) % $nshard;
	my $num = int(($docid - 1) / $nshard) + 1;
	my $ibx = $self->{shard2ibx}->[$shard];
	my $smsg = $ibx->over->get_art($num);
	return if $smsg->{bytes} == 0; # external message
	if ($ibx->can('msg_keywords')) {
		mitem_kw($self, $smsg, $mitem);
	}
	$smsg;
}

sub over {}

sub _check_mset_limit ($$$) {
	my ($lei, $desc, $mset) = @_;
	return if defined($lei->{opt}->{limit}); # user requested limit
	my $est = $mset->get_matches_estimated;
	my $tot = $lei->{mset_opt}->{total};
	$est > $tot and $lei->qerr(<<"");
# $desc estimated matches ($est) exceeds default --limit=$tot

}

sub _mset_more ($$) {
	my ($mset, $mo) = @_;
	my $size = $mset->size;
	$size >= $mo->{limit} && (($mo->{offset} += $size) < $mo->{total});
}

# $startq will see `q' in do_post_augment -> start_mua if spawning MUA.
# Otherwise $startq will EOF when do_augment is done augmenting and allow
# query_combined_mset and query_thread_mset to proceed.
sub wait_startq ($) {
	my ($lei) = @_;
	read(delete($lei->{startq}) // return, my $buf, 1) or return; # EOF
	die "BUG: wrote `$buf' to au_done" if $buf ne 'q';
	$lei->{opt}->{quiet} = 1;
	delete $lei->{opt}->{verbose};
	delete $lei->{-progress};
}

sub mset_progress {
	my $lei = shift;
	return if $lei->{early_mua} || !$lei->{-progress};
	if ($lei->{pkt_op_p}) {
		$lei->{pkt_op_p}->pkt_do('mset_progress', @_);
	} else { # single lei-daemon consumer
		my ($desc, $mset_size, $mset_total_est) = @_;
		$lei->{-mset_total} += $mset_size if $mset_total_est ne '?';
		$lei->qerr("# $desc $mset_size/$mset_total_est");
	}
}

sub sync_mset_cb { # async_mset cb
	my ($ret, $mset, $err) = @_;
	@$ret = ($mset, $err);
}

sub sync_mset ($$) {
	my ($srch, $mo) = @_;
	local $PublicInbox::DS::in_loop; # force synchronous
	$srch->async_mset($mo->{qstr}, $mo, \&sync_mset_cb, my $ret = []);
	my ($mset, $err) = @$ret;
	die $err if $err;
	$mset;
}

sub query_one_mset { # for --threads and l2m w/o sort
	my ($self, $ibxish) = @_;
	my $lei = $self->{lei};
	my $allow_sigs = PublicInbox::DS::allow_sigs qw(INT QUIT TERM);
	my ($srch, $over) = ($ibxish->search, $ibxish->over);
	my $dir = $ibxish->{inboxdir} // $ibxish->{topdir};
	return warn("$dir not indexed by Xapian\n") unless ($srch && $over);
	bless $srch, 'PublicInbox::LeiSearch'; # for ->qparse_new
	my $mo = { %{$lei->{mset_opt}} }; # copy
	local $0 = "$0 1 $mo->{qstr}";
	my $mset;
	my $each_smsg = $lei->{ovv}->ovv_each_smsg_cb($lei);
	my $can_kw = !!$ibxish->can('msg_keywords');
	my $threads = $lei->{opt}->{threads} // 0;
	my $fl = $threads > 1 ? 1 : undef;
	my $mid = $lei->{opt}->{'thread-id'};
	if (defined $mid) { # unknown $mid: no results, not a full search
		$mo->{threadid} = $over->mid2tid($mid) // return;
	}
	my $lss = $lei->{lss};
	my $maxk = "external.$dir.maxuid"; # max of previous, so our min
	my $min = $lss ? ($lss->{-cfg}->{$maxk} // 0) : 0;
	ref($min) and return warn("$maxk=$min has multiple values\n");
	($min =~ /[^0-9]/) and return warn("$maxk=$min not numeric\n");
	my $first_ids;
	do {
		$mset = eval { sync_mset $srch, $mo };
		return $lei->child_error(22 << 8, "E: $@") if $@; # 22 from curl
		mset_progress($lei, $dir, $mo->{offset} + $mset->size,
				$mset->get_matches_estimated);
		wait_startq($lei); # wait for keyword updates
		my $ids = $srch->mset_to_artnums($mset, $mo);
		my $i = 0;
		if ($threads) {
			# copy $ids if $lss since over->expand_thread
			# shifts @{$ctx->{ids}}
			$first_ids = [ @$ids ] if $lss;
			my $ctx = { ids => $ids, min => $min };
			my %n2item = map { $ids->[$i++] => $_ } $mset->items;
			while ($over->expand_thread($ctx)) { # fills {xids}
				for my $n (@{delete $ctx->{xids}}) {
					my $smsg = $over->get_art($n) or next;
					my $mi = delete $n2item{$n};
					next if $smsg->{bytes} == 0;
					if ($mi && $can_kw) {
						mitem_kw($srch, $smsg, $mi, $fl)
					} elsif ($mi && $fl) {
						# call ->xsmsg_vmd, later
						$smsg->{lei_q_tt_flagged} = 1;
					}
					$each_smsg->($smsg, $mi);
				}
			}
		} else {
			$first_ids = $ids;
			my @items = $mset->items; # parallel with @$ids
			for my $n (@$ids) {
				my $mitem = $items[$i++];
				next if $n <= $min;
				my $smsg = $over->get_art($n) or next;
				next if $smsg->{bytes} == 0;
				mitem_kw($srch, $smsg, $mitem, $fl) if $can_kw;
				$each_smsg->($smsg, $mitem);
			}
		}
	} while (_mset_more($mset, $mo));
	_check_mset_limit($lei, $dir, $mset);
	if ($lss && scalar(@$first_ids)) {
		my $max = $first_ids->[0];
		$lss->cfg_set($maxk, $max);
		undef $lss;
	}
	undef $each_smsg; # may commit
	$lei->{ovv}->ovv_atexit_child($lei);
}

sub query_combined_mset { # non-parallel for non-"--threads" users
	my ($self) = @_;
	my $lei = $self->{lei};
	my $allow_sigs = PublicInbox::DS::allow_sigs qw(INT QUIT TERM);
	my $mo = { %{$lei->{mset_opt}} };
	local $0 = "$0 C $mo->{qstr}";
	my $mset;
	for my $loc (locals($self)) {
		attach_external($self, $loc);
	}
	my $each_smsg = $lei->{ovv}->ovv_each_smsg_cb($lei);
	do {
		$mset = eval { sync_mset $self, $mo };
		return $lei->child_error(22 << 8, "E: $@") if $@; # 22 from curl
		mset_progress($lei, 'xsearch', $mo->{offset} + $mset->size,
				$mset->get_matches_estimated);
		wait_startq($lei); # wait for keyword updates
		for my $mitem ($mset->items) {
			my $smsg = smsg_for($self, $mitem) or next;
			$each_smsg->($smsg, $mitem);
		}
	} while (_mset_more($mset, $mo));
	_check_mset_limit($lei, 'xsearch', $mset);
	undef $each_smsg; # may commit
	$lei->{ovv}->ovv_atexit_child($lei);
}

sub _smsg_fill ($$) {
	my ($smsg, $eml) = @_;
	$smsg->populate($eml);
	$smsg->parse_references($eml, mids($eml));
	$smsg->{$_} //= '' for qw(from to cc ds subject references mid);
	delete @$smsg{qw(From Subject -ds -ts)};
}

sub each_remote_eml { # callback for MboxReader->mboxrd
	my ($eml, $self, $lei, $each_smsg) = @_;
	my $xoids = $lei->{ale}->xoids_for($eml, 1);
	my $smsg = bless {}, 'PublicInbox::Smsg';
	if ($self->{import_sto} && !$xoids) {
		my ($res, $kw) = $self->{import_sto}->wq_do('add_eml', $eml);
		if (ref($res) eq ref($smsg)) { # totally new message
			$smsg = $res;
			$self->{-sto_imported} = 1;
		}
		$smsg->{kw} = $kw; # short-circuit xsmsg_vmd
	}
	$smsg->{blob} //= $xoids ? (keys(%$xoids))[0]
				: $lei->git_oid($eml)->hexdigest;
	_smsg_fill($smsg, $eml);
	wait_startq($lei);
	my $nr = ++$lei->{-nr_remote_eml}; # needed for lss->cfg_set
	if ($lei->{-progress}) {
		my $now = now();
		my $next = $lei->{-next_progress} //= ($now + 1);
		if ($now > $next) {
			$lei->{-next_progress} = $now + 1;
			mset_progress($lei, $lei->{-current_url}, $nr, '?');
		}
	}
	$each_smsg->($smsg, undef, $eml);
}

sub fudge_qstr_time ($$$) {
	my ($lei, $uri, $qstr) = @_;
	return ($qstr, undef) unless $lei->{lss};
	my $cfg = $lei->{lss}->{-cfg} // die 'BUG: no lss->{-cfg}';
	my $cfg_key = "external.$uri.lastresult";
	my $lr = $cfg->{$cfg_key} or return ($qstr, $cfg_key);
	if ($lr !~ /\A\-?[0-9]+\z/) {
		$lei->child_error(0,
			"$cfg->{-f}: $cfg_key=$lr not an integer, ignoring");
		return ($qstr, $cfg_key);
	}
	my $rft = $lei->{opt}->{'remote-fudge-time'};
	if ($rft && $rft !~ /\A-?[0-9]+\z/) {
		my @t = $lei->{lss}->git->date_parse($rft);
		my $diff = time - $t[0];
		$lei->qerr("# $rft => $diff seconds");
		$rft = $diff;
	}
	$lr -= ($rft || (48 * 60 * 60));
	require PublicInbox::Admin;
	$lei->qerr("# $uri limiting to ".
		PublicInbox::Admin::fmt_localtime($lr).' and newer');
	# this should really be rt: (received-time), but no stable
	# public-inbox releases support it, yet.
	my $dt = 'dt:'.strftime('%Y%m%d%H%M%S', gmtime($lr)).'..';
	if ($qstr =~ /\S/) {
		substr($qstr, 0, 0, '(');
		$qstr .= ') AND ';
	}
	($qstr .= $dt, $cfg_key);
}

sub query_remote_mboxrd {
	my ($self, $uris) = @_;
	local $SIG{TERM} = sub { exit(0) }; # for DESTROY (File::Temp, $reap)
	my $allow_sigs = PublicInbox::DS::allow_sigs qw(INT QUIT TERM);
	my $lei = $self->{lei};
	my $opt = $lei->{opt};
	my $qstr = $lei->{mset_opt}->{qstr};
	local $0 = "$0 R $qstr";
	my @qform = (x => 'm');
	push(@qform, t => 1) if $opt->{threads};
	open my $cerr, '+>', undef;
	my $rdr = { 2 => $cerr };
	my @lbf_tee;
	if ($opt->{verbose}) {
		# spawn a line-buffered tee(1) script, otherwise curl
		# will write 1 character at-a-time and parallel outputs
		# mmmaaayyy llloookkk llliiikkkeee ttthhhiiisss
		# (n.b. POSIX tee(1) cannot do any buffering)
		my $o = { 1 => $cerr, 2 => $lei->{2} };
		delete $rdr->{2};
		@lbf_tee = ([ $^X, qw(-w -p -e), <<'' ], undef, $o);
BEGIN { $| = 1; use IO::Handle; STDERR->autoflush(1); }
print STDERR $_;

	}
	my $curl = PublicInbox::LeiCurl->new($lei, $self->{curl}) or return;
	push @$curl, '-s', '-d', '';
	my $each_smsg = $lei->{ovv}->ovv_each_smsg_cb($lei);
	$self->{import_sto} = $lei->{sto} if $lei->{opt}->{'import-remote'};
	if (defined(my $mid = $opt->{'thread-id'})) {
		$mid = mid_escape($mid);
		for my $uri (@$uris) {
			$uri->path($uri->path.$mid.'/');
		}
	}
	for my $uri (@$uris) {
		$lei->{-current_url} = $uri->as_string;
		my $start = time;
		my ($q, $key) = fudge_qstr_time($lei, $uri, $qstr);
		$uri->query_form(@qform, q => $q);
		my $cmd = $curl->for_uri($lei, $uri);
		$lei->qerr("# $cmd");
		$rdr->{2} //= popen_wr(@lbf_tee) if @lbf_tee;
		my $rd = popen_rd($cmd, undef, $rdr);
		my $fh = IO::Uncompress::Gunzip->new($rd, MultiStream => 1);
		eval {
			PublicInbox::MboxReader->mboxrd($fh, \&each_remote_eml,
						$self, $lei, $each_smsg);
		};
		my $exc = $@;
		$rd->close; # Gunzip won't close $rd on errors
		my $code = $?;
		$lei->sto_barrier_request if delete($self->{-sto_imported});
		my $nr = delete $lei->{-nr_remote_eml} // 0;
		# don't update if no results, maybe MTA is down
		if (!$code && !$exc) {
			$lei->{lss}->cfg_set($key, $start) if $key && $nr;
			mset_progress($lei, $lei->{-current_url}, $nr, $nr);
			next;
		}
		delete($rdr->{2})->close if @lbf_tee;
		seek($cerr, 0, SEEK_SET);
		read($cerr, my $err, -s $cerr);
		truncate($cerr, 0);
		next if (($code >> 8) == 22 && $err =~ /\b404\b/);
		$uri->query_form(q => $qstr);
		$lei->child_error($code, "E: <$uri> `$cmd` failed".
					($exc ? ": $exc" : ''));
	}
	undef $each_smsg;
	$lei->{ovv}->ovv_atexit_child($lei);
}

sub git { $_[0]->{git} // die 'BUG: git uninitialized' }

sub xsearch_done_wait { # awaitpid cb
	my ($pid, $wq, $lei) = @_;
	return if !$?;
	my $s = $? & 127;
	return $lei->child_error($?) if $s == 13 || $s == 15;
	$lei->child_error($?, 'non-fatal error from '.ref($wq)." \$?=$?");
}

sub query_done { # EOF callback for main daemon
	my ($lei) = @_;
	my $l2m = delete $lei->{l2m};
	delete $lei->{lxs};
	($lei->{opt}->{'mail-sync'} && !$lei->{sto}) and
		warn "BUG: {sto} missing with --mail-sync";
	$lei->sto_barrier_request;
	$lei->{ovv}->ovv_end($lei);
	if ($l2m) { # close() calls LeiToMail reap_compress
		$l2m->finish_output($lei);
		if ($l2m->lock_free) {
			$l2m->poke_dst;
			$lei->poke_mua;
		} else { # mbox users
			delete $l2m->{mbl}; # drop dotlock
		}
	}
	my $nr_w = delete($lei->{-nr_write}) // 0;
	my $nr_dup = (delete($lei->{-nr_seen}) // 0) - $nr_w;
	if ($lei->{-progress}) {
		my $tot = $lei->{-mset_total} // 0;
		my $x = "$tot matches";
		$x .= ", $nr_dup duplicates" if $nr_dup;
		if ($l2m) {
			my $m = "# $nr_w written to " .
				"$lei->{ovv}->{dst} ($x)";
			$nr_w ? $lei->qfin($m) : $lei->qerr($m);
		} else {
			$lei->qerr("# $x");
		}
	}
	$lei->start_mua if $l2m && !$l2m->lock_free;
	$lei->dclose;
}

sub post_augment_done { # via on_destroy in top-level lei-daemon
	my ($lei) = @_;
	my $err = delete $lei->{post_augment_err};
	if ($err) {
		if (my $lxs = delete $lei->{lxs}) {
			$lxs->wq_kill(-POSIX::SIGTERM());
			$lxs->wq_close;
		}
		$lei->fail("$err");
	}
	if (!$err && delete $lei->{early_mua}) { # non-augment case
		eval { $lei->start_mua }; # may trigger wait_startq
		$lei->fail($@) if $@;
	}
	close(delete $lei->{au_done}); # trigger wait_startq if start_mua didn't
}

sub do_post_augment {
	my ($lei) = @_;
	my $l2m = $lei->{l2m} or return; # client disconnected
	$l2m->post_augment($lei, on_destroy(\&post_augment_done, $lei));
}

sub incr_post_augment { # called whenever an l2m shard finishes augment
	my ($lei) = @_;
	my $l2m = $lei->{l2m} or return; # client disconnected
	return if ++$lei->{nr_post_augment} != $l2m->{-wq_nr_workers};
	do_post_augment($lei);
}

my $MAX_PER_HOST = 4;

sub concurrency {
	my ($self, $opt) = @_;
	my $nl = $opt->{threads} ? locals($self) : 1;
	my $nr = remotes($self);
	$nr = $MAX_PER_HOST if $nr > $MAX_PER_HOST;
	$nl + $nr;
}

sub start_query ($$) { # always runs in main (lei-daemon) process
	my ($self, $lei) = @_;
	local $PublicInbox::LEI::current_lei = $lei;
	if ($lei->{opt}->{threads} ||
			defined($lei->{opt}->{'thread-id'}) ||
			($lei->{l2m} && !$lei->{opt}->{'sort'})) {
		for my $ibxish (locals($self)) {
			$self->wq_io_do('query_one_mset', [], $ibxish);
		}
	} elsif (locals($self)) {
		$self->wq_io_do('query_combined_mset', []);
	}
	my $i = 0;
	my $q = [];
	for my $uri (remotes($self)) {
		push @{$q->[$i++ % $MAX_PER_HOST]}, $uri;
	}
	for my $uris (@$q) {
		$self->wq_io_do('query_remote_mboxrd', [], $uris);
	}
	if ($self->{-do_lcat}) {
		$self->wq_io_do('lcat_dump', []);
	}
	$self->wq_close; # lei_xsearch workers stop when done
}

sub incr_start_query { # called whenever an l2m shard starts do_post_auth
	my ($lei, $self) = @_;
	my $l2m = $lei->{l2m};
	return if ++$self->{nr_start_query} != $l2m->{-wq_nr_workers};
	start_query($self, $lei);
}

sub ipc_atfork_child {
	my ($self) = @_;
	$self->{lei}->_lei_atfork_child;
	$self->SUPER::ipc_atfork_child;
}

sub do_query {
	my ($self, $lei) = @_;
	my $l2m = $lei->{l2m};
	my $qstr = \($lei->{mset_opt}->{qstr});
	chomp $$qstr;
	$$qstr =~ s/[ \n\t]+/ /sg; # make URLs and $0 less ugly
	my $ops = {
		sigpipe_handler => [ $lei ],
		fail_handler => [ $lei ],
		do_post_augment => [ \&do_post_augment, $lei ],
		incr_post_augment => [ \&incr_post_augment, $lei ],
		'' => [ \&query_done, $lei ],
		mset_progress => [ \&mset_progress, $lei ],
		incr => [ $lei ],
		x_it => [ $lei ],
		child_error => [ $lei ],
		incr_start_query => [ \&incr_start_query, $lei, $self ],
	};
	$lei->{auth}->op_merge($ops, $l2m, $lei) if $l2m && $lei->{auth};
	my $end = $lei->pkt_op_pair;
	$lei->{1}->autoflush(1);
	$lei->start_pager if delete $lei->{need_pager};
	$lei->{ovv}->ovv_begin($lei);
	die 'BUG: xdb|over open' if $lei->{lse}->{xdb} || $lei->{lse}->{over};
	if ($l2m) {
		$l2m->pre_augment($lei);
		if ($lei->{opt}->{augment} && delete $lei->{early_mua}) {
			$lei->start_mua;
		}
		if ($l2m->{-wq_nr_workers} > 1 &&
				$l2m->{base_type} =~ /\A(?:maildir|mbox)\z/) {
			# setup two barriers to coordinate ->has_entries
			# between l2m workers
			pipe my $a_r, my $a_w;
			fcntl($a_r, $F_SETPIPE_SZ, 4096) if $F_SETPIPE_SZ;
			pipe my $b_r, my $b_w;
			fcntl($b_r, $F_SETPIPE_SZ, 4096) if $F_SETPIPE_SZ;
			$l2m->{au_peers} = [ $a_r, $a_w, $b_r, $b_w ];
		}
		$l2m->wq_workers_start('lei2mail', undef,
					$lei->oldset, { lei => $lei },
					\&xsearch_done_wait, $lei);
		pipe $lei->{startq}, $lei->{au_done};
		fcntl($lei->{startq}, $F_SETPIPE_SZ, 4096) if $F_SETPIPE_SZ;
		delete $l2m->{au_peers};
		close(delete $l2m->{-wq_s2}); # share wq_s1 with lei_xsearch
	}
	$self->wq_workers_start('lei_xsearch', undef,
				$lei->oldset, { lei => $lei },
				\&xsearch_done_wait, $lei);
	my $op_c = delete $lei->{pkt_op_c};
	delete $lei->{pkt_op_p};
	@$end = ();
	$self->{-do_lcat} = !!(delete $lei->{lcat_todo});
	if ($l2m) {
		$l2m->net_merge_all_done($lei) unless $lei->{auth};
	} else {
		start_query($self, $lei);
	}
	$lei->event_step_init; # wait for shutdowns
	$lei->wait_wq_events($op_c, $ops);
}

sub add_uri {
	my ($self, $uri) = @_;
	if (my $curl = $self->{curl} //= which('curl') // 0) {
		require PublicInbox::MboxReader;
		require IO::Uncompress::Gunzip;
		require PublicInbox::LeiCurl;
		push @{$self->{remotes}}, $uri;
		$uri;
	} else {
		warn "curl missing, ignoring $uri\n";
		undef;
	}
}

# returns URI or PublicInbox::Inbox-like object
sub prepare_external {
	my ($self, $loc, $boost) = @_; # n.b. already ordered by boost
	if (ref $loc) { # already a URI, or PublicInbox::Inbox-like object
		return add_uri($self, $loc) if $loc->can('scheme');
		# fall-through on Inbox-like objects
	} elsif ($loc =~ m!\Ahttps?://!) {
		require URI;
		return add_uri($self, URI->new($loc));
	} elsif (-f "$loc/ei.lock" && -d "$loc/ALL.git/objects") {
		require PublicInbox::ExtSearch;
		die "`\\n' not allowed in `$loc'\n" if index($loc, "\n") >= 0;
		$loc = PublicInbox::ExtSearch->new($loc);
	} elsif ((-f "$loc/inbox.lock" && -d "$loc/all.git/objects") ||
			(-d "$loc/public-inbox" && -d "$loc/objects")) {
		die "`\\n' not allowed in `$loc'\n" if index($loc, "\n") >= 0;
		require PublicInbox::Inbox; # v2, v1
		$loc = bless { inboxdir => $loc }, 'PublicInbox::Inbox';
	} elsif (!-e $loc) {
		warn "W: $loc gone, perhaps run: lei forget-external $loc\n";
		return undef;
	} else {
		warn "W: $loc ignored, unable to determine external type\n";
		return undef;
	}
	push @{$self->{locals}}, $loc;
	$loc;
}

sub _lcat_i { # LeiMailSync->each_src iterator callback
	my ($oidbin, $id, $each_smsg) = @_;
	$each_smsg->({blob => unpack('H*', $oidbin), pct => 100});
}

sub _lcat2smsg { # git->cat_async callback
	my ($bref, $oid, $type, $size, $smsg) = @_;
	if ($bref) {
		my $eml = PublicInbox::Eml->new($bref);
		my $json_dump = delete $smsg->{-json_dump};
		bless $smsg, 'PublicInbox::Smsg';
		_smsg_fill($smsg, $eml);
		$json_dump->($smsg, undef, $eml);
	}
}

sub lcat_dump { # via wq_io_do
	my ($self) = @_;
	my $lei = $self->{lei};
	my $allow_sigs = PublicInbox::DS::allow_sigs qw(INT QUIT TERM);
	my $each_smsg = $lei->{ovv}->ovv_each_smsg_cb($lei);
	my $git = $lei->{ale}->git;
	if (!$lei->{l2m}) {
		my $json_dump = $each_smsg;
		$each_smsg = sub {
			my ($smsg) = @_;
			$smsg->{-json_dump} = $json_dump;
			$git->cat_async($smsg->{blob}, \&_lcat2smsg, $smsg);
		};
	}
	my $lms;
	for my $ent (@{$lei->{lcat_todo}}) {
		if (ref $ent eq 'HASH') { # { fid => $fid ,.. }
			$lms //= $lei->{lse}->lms;
			$lms->each_src($ent, \&_lcat_i, $each_smsg);
		} else { # oidhex
			$each_smsg->({ blob => $ent, pct => 100 });
		}
	}
	$git->async_wait_all;
	undef $each_smsg; # may commit
	$lei->{ovv}->ovv_atexit_child($lei);
}

1;
