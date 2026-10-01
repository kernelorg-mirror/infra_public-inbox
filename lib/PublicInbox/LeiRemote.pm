# Copyright (C) all contributors <meta@public-inbox.org>
# License: AGPL-3.0+ <https://www.gnu.org/licenses/agpl-3.0.txt>

# Make remote externals HTTP(S) inboxes behave like
# PublicInbox::Inbox and PublicInbox::Search/ExtSearch.
# This exists solely for SolverGit.  It is a high-latency a
# synchronous API that is not at all fast.
package PublicInbox::LeiRemote;
use v5.10.1;
use strict;
use IO::Uncompress::Gunzip;
use PublicInbox::MboxReader;
use PublicInbox::Spawn qw(popen_rd);
use PublicInbox::LeiCurl;
use PublicInbox::ContentHash qw(git_sha);

sub new {
	my ($cls, $lei, $uri) = @_;
	bless { uri => $uri, lei => $lei }, $cls;
}

sub isrch { $_[0] } # SolverGit expcets this

sub each_mboxrd_eml { # callback for MboxReader->mboxrd
	my ($eml, $self) = @_;
	my $lei = $self->{lei};
	my $xoids = $lei->{ale}->xoids_for($eml, 1);
	my $smsg = bless {}, 'PublicInbox::Smsg';
	if ($lei->{sto} && !$xoids) { # memoize locally
		my $res = $lei->{sto}->wq_do('add_eml', $eml);
		$smsg = $res if ref($res) eq ref($smsg);
	}
	$smsg->{blob} //= $xoids ? (keys(%$xoids))[0]
				: $lei->git_oid($eml)->hexdigest;
	$smsg->populate($eml);
	$smsg->{mid} //= '(none)';
	push @{$self->{smsg}}, $smsg;
}

sub mset {
	my ($self, $qstr, undef) = @_; # $opt ($_[2]) ignored
	my $lei = $self->{lei};
	my $curl = PublicInbox::LeiCurl->new($lei, $lei->{curl});
	push @$curl, '-s', '-d', '';
	my $uri = $self->{uri}->clone;
	$uri->query_form(q => $qstr, x => 'm', r => 1); # r=1: relevance
	my $cmd = $curl->for_uri($self->{lei}, $uri);
	$self->{lei}->qerr("# $cmd");
	$self->{smsg} = [];
	my $rd = popen_rd($cmd, undef, { 2 => $lei->{2} });
	my $fh = IO::Uncompress::Gunzip->new($rd, MultiStream => 1);
	eval { PublicInbox::MboxReader->mboxrd($fh, \&each_mboxrd_eml, $self) };
	my $err = $@ ? ": $@" : '';
	$rd->close; # Gunzip won't close $rd on errors
	my $code = $?;
	my $wait = $self->{lei}->{sto}->wq_do('barrier');
	$lei->child_error($code, "@$cmd failed$err") if $err || $code;
	$self; # we are the mset (and $ibx, and $self)
}

# fake support for async API
sub async_mset {
	my ($self, $qry, undef, $cb, @arg) = @_; # $opt ($_[2]) ignored
	my $mset;
	for my $qstr (ref($qry) eq 'ARRAY' ? @$qry : ($qry)) {
		$mset = eval { mset($self, $qstr) };
		last if $mset && $mset->size;
	}
	$mset ? $cb->(@arg, $mset) : $cb->(@arg, undef, $@ || 'err');
	undef;
}

sub size { scalar @{$_[0]->{smsg}} } # size of previous results

sub mset_to_smsg {
	my ($self, $ibx, $mset) = @_; # all 3 are $self
	wantarray ? ($self->size, @{$self->{smsg}}) : $self->{smsg};
}

sub base_url { "$_[0]->{uri}" }

sub smsg_eml {
	my ($self, $smsg) = @_;
	my $bref = $self->{lei}->ale->git->cat_file($smsg->{blob}) // do {
		my $lms = $self->{lei}->lms;
		($lms ? $lms->local_blob($smsg->{blob}, 1) : undef) // do {
			my $sto = $self->{lei}->{sto} //
					$self->{lei}->_lei_store;
			$sto && $sto->{-wq_s1} ?
				$sto->wq_do('cat_blob', $smsg->{blob}) : undef;
		}
	};
	return PublicInbox::Eml->new($bref) if $bref;
	warn("E: $self->{uri} $smsg->{blob} gone <$smsg->{mid}>\n");
	undef;
}

1;
