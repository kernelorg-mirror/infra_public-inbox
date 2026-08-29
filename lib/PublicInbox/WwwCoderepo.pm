# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>
#
# Standalone code repository viewer for users w/o cgit.
# This isn't intended to replicate all of cgit, but merely to be a
# "good enough" viewer with search support and some UI hints to encourage
# cloning + command-line usage.
package PublicInbox::WwwCoderepo;
use v5.12;
use parent qw(PublicInbox::WwwStream);
use File::Temp 0.19 (); # newdir
use POSIX qw(O_RDWR F_GETFL);
use PublicInbox::ViewVCS;
use PublicInbox::WwwStatic qw(r);
use PublicInbox::GitHTTPBackend;
use PublicInbox::WwwStream;
use PublicInbox::Hval qw(prurl ascii_html utf8_maybe);
use PublicInbox::ViewDiff qw(uri_escape_path);
use PublicInbox::RepoSnapshot;
use PublicInbox::RepoAtom;
use PublicInbox::RepoTree;
use PublicInbox::RepoList;
use PublicInbox::OnDestroy;
use URI::Escape qw(uri_escape_utf8);
use autodie qw(fcntl open);
use PublicInbox::Git qw(git_exe);

my @EACH_REF = (git_exe, qw(for-each-ref --sort=-creatordate),
		"--format=%(HEAD)%00".join('%00', map { "%($_)" }
		qw(objectname refname:short subject creatordate:short)));
my $HEADS_CMD = <<'';
# heads (aka `branches'):
$ git for-each-ref --sort=-creatordate refs/heads \
	--format='%(HEAD) %(refname:short) %(subject) (%(creatordate:short))'

my $TAGS_CMD = <<'';
# tags:
$ git for-each-ref --sort=-creatordate refs/tags \
	--format='%(refname:short) %(subject) (%(creatordate:short))'

my $NO_HEADS = "# no heads (branches), yet...\n";
my $NO_TAGS = "# no tags, yet...\n";

# shared with PublicInbox::Cgit
sub prepare_coderepos {
	my ($self) = @_;
	my $pi_cfg = $self->{pi_cfg};

	# TODO: support gitweb and other repository viewers?
	$pi_cfg->parse_cgitrc(undef, 0);

	my $coderepos = $pi_cfg->{-coderepos};
	for my $k (grep(/\Acoderepo\.(?:.+)\.dir\z/, keys %$pi_cfg)) {
		$k = substr($k, length('coderepo.'), -length('.dir'));
		$coderepos->{$k} //= $pi_cfg->fill_coderepo($k);
	}

	# associate inboxes and extindices with coderepos for search:
	for my $k (grep(/\Apublicinbox\.(?:.+)\.coderepo\z/, keys %$pi_cfg)) {
		$k = substr($k, length('publicinbox.'), -length('.coderepo'));
		my $ibx = $pi_cfg->lookup_name($k) // next;
		$pi_cfg->repo_objs($ibx);
	}
	for my $k (grep(/\Aextindex\.(?:.+)\.coderepo\z/, keys %$pi_cfg)) {
		$k = substr($k, length('extindex.'), -length('.coderepo'));
		my $eidx = $pi_cfg->lookup_ei($k) // next;
		$pi_cfg->repo_objs($eidx);
	}
	$pi_cfg->each_cindex('load_coderepos', $pi_cfg);
}

sub new {
	my ($cls, $pi_cfg) = @_;
	my $self = bless { pi_cfg => $pi_cfg }, $cls;
	prepare_coderepos($self);
	$self->{snapshots} = do {
		my $s = $pi_cfg->{'coderepo.snapshots'} // '';
		$s eq 'all' ? \%PublicInbox::RepoSnapshot::FMT_TYPES :
			+{ map { $_ => 1 } split(/\s+/, $s) };
	};
	$self->{$_} = 10 for qw(summary_branches summary_tags);
	$self->{$_} = 10 for qw(summary_log);

	# try reuse STDIN if it's already /dev/null
	open $self->{log_fh}, '+>', '/dev/null';
	my @l = stat($self->{log_fh}) or die "stat: $!";
	my @s = stat(STDIN) or die "stat(STDIN): $!";
	if ("@l[0, 1]" eq "@s[0, 1]") {
		my $f = fcntl(STDIN, F_GETFL, 0);
		$self->{log_fh} = \*STDIN if $f & O_RDWR;
	}
	$self;
}

sub _snapshot_link_prep {
	my ($ctx) = @_;
	my @s = sort keys %{$ctx->{wcr}->{snapshots}} or return ();
	my $n = $ctx->{git}->local_nick // die "BUG: $ctx->{git_dir} nick";
	$n =~ s!\.git/*\z!!;
	($n) = ($n =~ m!([^/]+)/*\z!);
	(ascii_html($n).'-', @s);
}

sub _refs_heads_link {
	my ($line, $upfx) = @_;
	my ($pfx, $oid, $ref, $s, $cd) = split(/\0/, $line);
	my $align = length($ref) < 12 ? ' ' x (12 - length($ref)) : '';
	("$pfx <a\nhref=$upfx$oid/s/>", ascii_html($ref),
		"</a>$align ", ascii_html($s), " ($cd)\n")
}

sub _refs_tags_link {
	my ($line, $upfx, $snap_pfx, @snap_fmt) = @_;
	my (undef, $oid, $ref, $s, $cd) = split(/\0/, $line);
	my $align = length($ref) < 12 ? ' ' x (12 - length($ref)) : '';
	if (@snap_fmt) {
		my $v = $ref;
		$v =~ s/\A[vV]//;
		@snap_fmt = map {
			qq{ <a href="${upfx}snapshot/$snap_pfx$v.$_">$_</a>}
		} @snap_fmt;
	}
	("<a\nhref=$upfx$oid/s/>", ascii_html($ref),
		"</a>$align ", ascii_html($s), " ($cd)", @snap_fmt, "\n");
}

sub emit_joined_inboxes ($) {
	my ($ctx) = @_;
	my $names = $ctx->{git}->{ibx_names}; # coderepo directives in config
	my $score = $ctx->{git}->{ibx_score}; # generated w/ cindex --join
	($names || $score) or return;
	my $pi_cfg = $ctx->{wcr}->{pi_cfg};
	my ($u, $h);
	my $zfh = $ctx->zfh;
	print $zfh "\n# associated public inboxes:",
		"\n# (number on the left is used for dev purposes)";
	my @ns = map { [ 0, $_ ] } @$names;
	my $env = $ctx->{env};
	for (@ns, @$score) {
		my ($nr, $name) = @$_;
		my $ibx = $pi_cfg->lookup_name($name) // do {
			warn "W: inbox `$name' gone for $ctx->{git}->{git_dir}";
			say $zfh '# ', ascii_html($name), ' (missing inbox?)';
			next;
		};
		if (scalar(@{$ibx->{url} // []})) {
			$u = $h = ascii_html(prurl($env, $ibx->{url}));
		} else {
			$h = ascii_html(prurl($env, uri_escape_utf8($name)));
			$h .= '/';
			$u = ascii_html($name);
		}
		if ($nr) {
			printf $zfh "\n% 11u", $nr;
		} else {
			print $zfh "\n", ' 'x11;
		}
		print $zfh qq{ <a\nhref="$h">$u</a>};
	}
}

sub summary_END { # called via OnDestroy
	my ($ctx) = @_;
	my $wcb = delete($ctx->{-wcb}) or return; # already done
	PublicInbox::WwwStream::html_init($ctx);
	my $zfh = $ctx->zfh;

	my @r = split(/\n/s, delete($ctx->{qx_res}->{'log'}) // '');
	my $last = scalar(@r) > $ctx->{wcr}->{summary_log} ? pop(@r) : undef;
	my $tip_html = '';
	my $tip = $ctx->{qp}->{h};
	$tip_html .= ' '.ascii_html($tip).' --' if defined $tip;
	print $zfh <<EOM;
<pre><a id=log>\$</a> git log --pretty=format:'%h %s (%cs)%d'$tip_html
EOM
	for (@r) {
		my $d; # decorations
		s/^ \(([^\)]+)\)// and $d = $1;
		substr($_, 0, 1, '');
		my ($H, $h, $cs, $s) = split(/ /, $_, 4);
		print $zfh "<a\nhref=./$H/s/>$h</a> ", ascii_html($s),
			" (", $cs, ")\n";
		print $zfh "\t(", ascii_html($d), ")\n" if $d;
	}
	print $zfh '# no commits in `', ($tip//'HEAD'),"', yet\n\n" if !@r;
	print $zfh "...\n" if $last;

	# README
	my ($bref, $oid, $ref_path) = @{delete $ctx->{qx_res}->{readme} // []};
	if ($bref) {
		my $l = PublicInbox::Linkify->new;
		$$bref =~ s/\s*\z//sm;
		my (undef, $path) = split(/:/, $ref_path, 2); # HEAD:README
		print $zfh "\n<a id=readme>\$</a> " .
			qq(git cat-file blob <a href="./$oid/s/?b=) .
			ascii_html(uri_escape_path($path)) . q(">).
			ascii_html($ref_path), "</a>\n",
			$l->to_html($$bref), '</pre><hr><pre>';
	}

	# refs/heads
	print $zfh '<a id=heads>', $HEADS_CMD , '</a>';
	@r = split(/^/sm, delete($ctx->{qx_res}->{heads}) // '');
	$last = scalar(@r) > $ctx->{wcr}->{summary_branches} ? pop(@r) : undef;
	chomp(@r);
	for (@r) { print $zfh _refs_heads_link($_, './') }
	print $zfh $NO_HEADS if !@r;
	print $zfh qq(<a href="refs/heads/">...</a>\n) if $last;
	print $zfh "\n<a id=tags>", $TAGS_CMD, '</a>';
	@r = split(/^/sm, delete($ctx->{qx_res}->{tags}) // '');
	$last = scalar(@r) > $ctx->{wcr}->{summary_tags} ? pop(@r) : undef;
	my ($snap_pfx, @snap_fmt) = _snapshot_link_prep($ctx);
	chomp @r;
	for (@r) { print $zfh _refs_tags_link($_, './', $snap_pfx, @snap_fmt) }
	print $zfh $NO_TAGS if !@r;
	print $zfh qq(<a href="refs/tags/">...</a>\n) if $last;
	emit_joined_inboxes $ctx;
	$wcb->($ctx->html_done('</pre>'));
}

sub capture { # psgi_qx callback to capture git-for-each-ref
	my ($bref, $ctx, $key) = @_; #  $_[3] = OnDestroy(summary_END)
	utf8::decode($$bref);
	$ctx->{qx_res}->{$key} = $$bref;
	# summary_END may be called via OnDestroy $arg->[2]
}

sub set_readme { # git->cat_async callback
	my ($bref, $oid, $type, $size, $ctx) = @_;
	my $ref_path = shift @{$ctx->{-readme_tries}}; # e.g. HEAD:README
	if ($type eq 'blob' && !$ctx->{qx_res}->{readme}) {
		utf8::decode($$bref);
		$ctx->{qx_res}->{readme} = [ $bref, $oid, $ref_path ];
	} elsif (scalar @{$ctx->{-readme_tries}} == 0) {
		$ctx->{qx_res}->{readme} //= []; # nothing left to try
	} # or try another README...
	# summary_END may be called via OnDestroy ($ctx->{-END})
}

sub summary ($$) {
	my ($ctx, $wcb) = @_;
	$ctx->{-wcb} = $wcb; # PublicInbox::HTTP::{Identity,Chunked}
	my $tip = $ctx->{qp}->{h}; # same as cgit
	if (defined $tip && $tip eq '') {
		delete $ctx->{qp}->{h};
		undef($tip);
	}
	my ($nb, $nt, $nl) = map { $_ + 1 } @{$ctx->{wcr}}{qw(
		summary_branches summary_tags summary_log)};
	$ctx->{qx_res} = {};
	my $qsp_err = \($ctx->{-qsp_err} = '');
	my %opt = (quiet => 1, 2 => $ctx->{wcr}->{log_fh});
	my %env = (GIT_DIR => $ctx->{git}->{git_dir});
	my @log = (git_exe, 'log', "-$nl", '--pretty=format:%d %H %h %cs %s');
	push(@log, $tip) if defined $tip;

	# limit scope for MockHTTP test (t/solver_git.t)
	my $END = on_destroy \&summary_END, $ctx;
	for (['log', \@log],
		 [ 'heads', [@EACH_REF, "--count=$nb", 'refs/heads'] ],
		 [ 'tags', [@EACH_REF, "--count=$nt", 'refs/tags'] ]) {
		my ($k, $cmd) = @$_;
		my $qsp = PublicInbox::Qspawn->new($cmd, \%env, \%opt);
		$qsp->{qsp_err} = $qsp_err;
		$qsp->psgi_qx($ctx->{env}, undef, \&capture, $ctx, $k, $END);
	}
	$tip //= 'HEAD';
	my @try = ("$tip:README", "$tip:README.md"); # TODO: configurable
	my %ctx = (%$ctx, -END => $END, -readme_tries => [ @try ]);
	PublicInbox::ViewVCS::do_cat_async(\%ctx, \&set_readme, @try);
}

# called by GzipFilter->close after translate
sub zflush { $_[0]->SUPER::zflush('</pre>', $_[0]->_html_end) }

# called by GzipFilter->write or GetlineResponse->getline
sub translate {
	my $ctx = shift;
	$_[0] // return zflush($ctx); # getline caller
	my @out;
	my $fbuf = delete($ctx->{fbuf}) // shift;
	$fbuf .= shift while @_;
	if ($ctx->{-heads}) {
		while ($fbuf =~ s/\A([^\n]+)\n//s) {
			utf8_maybe(my $x = $1);
			push @out, _refs_heads_link($x, '../../');
		}
	} else {
		my ($snap_pfx, @snap_fmt) = _snapshot_link_prep($ctx);
		while ($fbuf =~ s/\A([^\n]+)\n//s) {
			utf8_maybe(my $x = $1);
			push @out, _refs_tags_link($x, '../../',
						$snap_pfx, @snap_fmt);
		}
	}
	$ctx->{fbuf} = $fbuf; # may be incomplete
	@out ? $ctx->SUPER::translate(@out) : ''; # not EOF, yet
}

sub _refs_parse_hdr { # {parse_hdr} for Qspawn
	my ($r, $bref, $ctx) = @_;
	my ($code, $top);
	if ($r == 0) {
		$code = 404;
		$top = $ctx->{-heads} ? $NO_HEADS : $NO_TAGS;
	} else {
		$code = 200;
		$top = $ctx->{-heads} ? $HEADS_CMD : $TAGS_CMD;
	}
	PublicInbox::WwwStream::html_init($ctx);
	bless $ctx, __PACKAGE__; # re-bless for ->translate
	print { $ctx->{zfh} } '<pre>', $top;
	[ $code, delete($ctx->{-res_hdr}), $ctx ]; # [2] is qspawn.filter
}

sub refs_foo { # /$REPO/refs/{heads,tags} endpoints
	my ($self, $ctx, $pfx) = @_;
	$ctx->{wcr} = $self;
	$ctx->{-upfx} = '../../';
	$ctx->{-heads} = 1 if $pfx eq 'refs/heads';
	my $qsp = PublicInbox::Qspawn->new([@EACH_REF, $pfx ],
					{ GIT_DIR => $ctx->{git}->{git_dir} });
	$qsp->psgi_yield($ctx->{env}, undef, \&_refs_parse_hdr, $ctx);
}

sub _get_css ($$) {
	my ($ctx, $key) = @_;
	$ctx->{www}->{-css_map} // $ctx->{www}->stylesheets_prepare('');
	PublicInbox::WWW::srv_css_rec $ctx->{www}->{-css_map}->{$key};
}

sub srv { # endpoint called by PublicInbox::WWW
	my ($self, $ctx) = @_;
	my $path_info = $ctx->{env}->{PATH_INFO};
	my $git;
	# handle clone requests
	my $pi_cfg = $self->{pi_cfg};
	if ($path_info =~ m!\A/(.+?)/($PublicInbox::GitHTTPBackend::ANY)\z!x and
		($git = $pi_cfg->get_coderepo($1))) {
			PublicInbox::GitHTTPBackend::serve($ctx->{env},
							$git, $2, $pi_cfg);
	} elsif ($path_info =~ m!\A/(.+?)/\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		$ctx->{wcr} = $self;
		sub { summary($ctx, $_[0]) }; # $_[0] = wcb
	} elsif ($path_info =~ m!\A/(.+?)/([a-f0-9]+)/s/([^/]+)?\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		$ctx->{lh} = $self->{log_fh};
		PublicInbox::ViewVCS::show($ctx, $2, $3);
	} elsif ($path_info =~ m!\A/(.+?)/tree/(.*)\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		$ctx->{lh} = $self->{log_fh};
		PublicInbox::RepoTree::srv_tree($ctx, $2) // r(404);
	} elsif ($path_info =~ m!\A/(.+?)/snapshot/([^/]+)\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		$ctx->{wcr} = $self;
		PublicInbox::RepoSnapshot::srv($ctx, $2) // r(404);
	} elsif ($path_info =~ m!\A/(.+?)/atom/(.*)\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		$ctx->{lh} = $self->{log_fh};
		PublicInbox::RepoAtom::srv_atom($ctx, $2) // r(404);
	} elsif ($path_info =~ m!\A/(.+?)/tags\.atom\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		PublicInbox::RepoAtom::srv_tags_atom($ctx);
	} elsif ($path_info =~ m!\A/(.+?)/(refs/(?:heads|tags))/\z! and
			($ctx->{git} = $pi_cfg->get_coderepo($1))) {
		refs_foo($self, $ctx, $2);
	} elsif ($path_info =~ m!\A/(.+?)/([a-zA-Z0-9_\-\.]+)\.css\z! &&
			$pi_cfg->get_coderepo($1)) {
		_get_css $ctx, $2;
	} elsif ($path_info =~ m!\A/(.*?\*.*?)/*\z!) {
		my $re = PublicInbox::Config::glob2re($1);
		PublicInbox::RepoList::html($self, $ctx, qr!$re\z!) // r(404);
	} elsif ($path_info =~ m!\A/(.+?)/\z!) {
		my $re = qr!\A\Q$1\E/!;
		PublicInbox::RepoList::html($self, $ctx, $re) // r(404);
	} elsif ($path_info =~ m!\A/(.+?)\z! and
			($git = $pi_cfg->get_coderepo($1))) {
		my $qs = $ctx->{env}->{QUERY_STRING};
		my $url = $git->base_url($ctx->{env});
		$url .= "?$qs" if $qs ne '';
		[ 301, [ Location => $url, 'Content-Type' => 'text/plain' ],
			[ "Redirecting to $url\n" ] ];
	} else {
		r(404);
	}
}

1;
