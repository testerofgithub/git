# gitweb - simple web interface to track changes in git repositories
#
# (C) 2006, John 'Warthog9' Hawley <warthog19@eaglescrag.net>
#
# This program is licensed under the GPLv2

#
# Gitweb caching engine
#

#use File::Path qw(make_path remove_tree);
use File::Path qw(mkpath rmtree); # Used for compatability reasons
use Digest::MD5 qw(md5 md5_hex md5_base64);
use Fcntl ':flock';
use File::Copy;

sub cache_fetch {
	my ($action) = @_;
	my $cacheTime = 0;

	if(! -d $cachedir){
		print "*** Warning ***: Caching enabled but cache directory does not exsist.  ($cachedir)\n";
		mkdir ("cache", 0755) || die "Cannot create cache dir - you will need to manually create";
		print "Cache directory created successfully\n";
	}

	our $full_url = "$my_url?". $ENV{'QUERY_STRING'};
	our $urlhash = md5_hex($full_url);
	our $fullhashdir = "$cachedir/". substr( $urlhash, 0, 2) ."/";

	eval { mkpath( $fullhashdir, 0, 0777 ) };
	if ($@) {
		die_error(500, "Internal Server Error", "Could not create cache directory: $@");
	}
	$fullhashpath = "$fullhashdir/". substr( $urlhash, 2 );
	$fullhashbinpath = "$fullhashpath.bin.wt";
	$fullhashbinpathfinal = "$fullhashpath.bin";

	if(! -e "$fullhashpath" ){
		if(! $cacheDoFork || ! defined(my $childPid = fork()) ){
			cacheUpdate($action,0);
			cacheDisplay($action);
		} elsif ( $childPid == 0 ){
			#run the updater
			cacheUpdate($action,1);
		}else{
			cacheWaitForUpdate($action);
		}
	}else{
		#if cache is out dated, update
		#else displayCache();
		open(cacheFile, '<', "$fullhashpath");
		stat(cacheFile);
		close(cacheFile);
		my $stat_time = (stat(_))[9];
		my $stat_size = (stat(_))[7];

		$cacheTime = get_loadavg() * 60;
		if( $cacheTime > $maxCacheTime ){
			$cacheTime = $maxCacheTime;
		}
		if( $cacheTime < $minCacheTime ){
			$cacheTime = $minCacheTime;
		}
		if( $stat_time < (time - $cacheTime) || $stat_size == 0 ){
			if( ! $cacheDoFork || ! defined(my $childPid = fork()) ){
				cacheUpdate($action,0);
				cacheDisplay($action);
			} elsif ( $childPid == 0 ){
				#run the updater
				#print "Running updater\n";
				cacheUpdate($action,1);
			}else{
				#print "Waiting for update\n";
				cacheWaitForUpdate($action);
			}
		} else {
			cacheDisplay($action);
		}


	}

	#
	# If all of the caching failes - lets go ahead and press on without it and fall back to 'default'
	# non-caching behavior.  This is the softest of the failure conditions.
	#
	#$actions{$action}->();
}

sub cacheUpdate {
	my ($action,$areForked) = @_;
	my $lockingStatus;
	my $fileData = "";

	if($backgroundCache){
		open(cacheFileBG, '>:utf8', "$fullhashpath.bg");
		my $lockStatBG = flock(cacheFileBG,LOCK_EX|LOCK_NB);

		$lockStatus = $lockStatBG;
	}else{
		open(cacheFile, '>:utf8', $fullhashpath);
		my $lockStat = flock(cacheFile,LOCK_EX|LOCK_NB);

		$lockStatus = $lockStat;
	}
	#print "lock status: $lockStat\n";


	if (! $lockStatus ){
		if ( $areForked ){
			exit(0);
		}else{
			return;
		}
	}

	if(
		$action eq "snapshot"
		||
		$action eq "blob_plain"
	){
		my $openstat = open(cacheFileBinWT, '>>:utf8', "$fullhashbinpath");
		my $lockStatBin = flock(cacheFileBinWT,LOCK_EX|LOCK_NB);
	}

	# Trap all output from the action
	change_output();

	$actions{$action}->();

	# Reset the outputs as we should be fine now
	reset_output();


	if($backgroundCache){
		open(cacheFile, '>:utf8', "$fullhashpath");
		$lockStat = flock(cacheFile,LOCK_EX);

		if (! $lockStat ){
			if ( $areForked ){
				exit(0);
			}else{
				return;
			}
		}
	}

	if(
		$action eq "snapshot"
		||
		$action eq "blob_plain"
	){
		my $openstat = open(cacheFileBinFINAL, '>:utf8', "$fullhashbinpathfinal");
		$lockStatBIN = flock(cacheFileBinFINAL,LOCK_EX);

		if (! $lockStatBIN ){
			if ( $areForked ){
				exit(0);
			}else{
				return;
			}
		}
	}

	# Actually dump the output to the proper file handler
	local $/ = undef;
	$|++;
	print cacheFile "$output";
	$|--;
	if(
		$action eq "snapshot"
		||
		$action eq "blob_plain"
	){
		move("$fullhashbinpath", "$fullhashbinpathfinal") or die "Binary Cache file could not be updated: $!";

		flock(cacheFileBinFINAL,LOCK_UN);
		close(cacheFileBinFINAL);

		flock(cacheFileBinWT,LOCK_UN);
		close(cacheFileBinWT);
	}

	flock(cacheFile,LOCK_UN);
	close(cacheFile);

	if($backgroundCache){
		flock(cacheFileBG,LOCK_UN);
		close(cacheFileBG);
	}

	if ( $areForked ){
		exit(0);
	} else {
		return;
	}
}


sub cacheWaitForUpdate {
	my ($action) = @_;
	my $x = 0;
	my $max = 10;
	my $lockStat = 0;

	if( $backgroundCache ){
		if( -e "$fullhashpath" ){
			open(cacheFile, '<:utf8', "$fullhashpath");
			$lockStat = flock(cacheFile,LOCK_SH|LOCK_NB);
			stat(cacheFile);
			close(cacheFile);

			if( $lockStat && ( (stat(_))[9] > (time - $maxCacheLife) ) ){
				cacheDisplay($action);
				return;
			}
		}
	}

	if(
		$action eq "atom"
		||
		$action eq "rss"
		||
		$action eq "opml"
	){
		do {
			sleep 2 if $x > 0;
			open(cacheFile, '<:utf8', "$fullhashpath");
			$lockStat = flock(cacheFile,LOCK_SH|LOCK_NB);
			close(cacheFile);
			$x++;
			$combinedLockStat = $lockStat;
		} while ((! $combinedLockStat) && ($x < $max));

		if( $x != $max ){
			cacheDisplay($action);
		}
		return;
	}

	$| = 1;

	print $::cgi->header(
				-type=>'text/html',
				-charset => 'utf-8',
				-status=> 200,
				-expires => 'now',
				# HTTP/1.0
				-Pragma => 'no-cache',
				# HTTP/1.1
				-Cache_Control => join(
							', ',
							qw(
								private
								no-cache
								no-store
								must-revalidate
								max-age=0
								pre-check=0
								post-check=0
							)
						)
				);

	print <<EOF;
<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www/w3.porg/TR/html4/strict.dtd">
<!-- git web w/caching interface version $version, (C) 2006-2010, John 'Warthog9' Hawley <warthog9\@kernel.org> -->
<!-- git core binaries version $git_version -->
<head>
<meta http-equiv="content-type" content="$content_type; charset=utf-8"/>
<meta name="generator" content="gitweb/$version git/$git_version"/>
<meta name="robots" content="index, nofollow"/>
<meta http-equiv="refresh" content="0"/>
<title>$title</title>
</head>
<body>
EOF

	print "Generating..";
	do {
		print ".";
		sleep 2 if $x > 0;
		open(cacheFile, '<:utf8', "$fullhashpath");
		$lockStat = flock(cacheFile,LOCK_SH|LOCK_NB);
		close(cacheFile);
		$x++;
		$combinedLockStat = $lockStat;
	} while ((! $combinedLockStat) && ($x < $max));
	print <<EOF;
</body>
</html>
EOF
	return;
}

sub cacheDisplay {
	local $/ = undef;
	$|++;

	my ($action) = @_;
	open(cacheFile, '<:utf8', "$fullhashpath");
	$lockStat = flock(cacheFile,LOCK_SH|LOCK_NB);

	if (! $lockStat ){
		close(cacheFile);
		cacheWaitForUpdate($action);
	}

	if(
		(
			$action eq "snapshot"
			||
			$action eq "blob_plain"
		)
	){
		my $openstat = open(cacheFileBin, '<', "$fullhashbinpathfinal");
		$lockStatBIN = flock(cacheFileBin,LOCK_SH|LOCK_NB);
		if (! $lockStatBIN ){
			system ("echo 'cacheDisplay - bailing due to binary lock failure' >> /tmp/gitweb.log");
			close(cacheFile);
			close(cacheFileBin);
			cacheWaitForUpdate($action);
		}

		my $binfilesize = -s "$fullhashbinpathfinal";
		print "Content-Length: $binfilesize";
	}
	while( <cacheFile> ){
		print $_;
	}
	if(
		$action eq "snapshot"
		||
		$action eq "blob_plain"
	){
		binmode STDOUT, ':raw';
		print <cacheFileBin>;
		binmode STDOUT, ':utf8'; # as set at the beginning of gitweb.cgi
		close(cacheFileBin);
	}
	close(cacheFile);
	$|--;
}

1;
__END__
