#!/usr/bin/perl
# Script to install signed packages created and distributed by distribute.pl.
# Written 3, 5 February 2022 by Jim Lippard.
# Modified 5 February 2023 by Jim Lippard to verify OpenBSD-signed
#    packages against listed public keys, not just verify the name.
# Modified 14 March 2023 by Jim Lippard to support file versons with flavors,
#    like emacs-20.8p0-no_x11.tgz.
# Modified 4 January 2024 by Jim Lippard to use pledge/unveil. Of limited
#    value but slightly more useful than in distribute.pl.
# Modified 5 January 2024 by Jim Lippard to rework signify signature
#    validation in pledge/unveil environment and be more robust.
#    Developed for distribute.pl.) Requires temp directory.
#    Also modified to use specific groups for syslock and unlock.
# Modified 7 January 2024 by Jim Lippard to support annual keys and
#    new OpenBSD pkg_add "-pkg" requirement in key name.
# Modified 28 July 2024 by Jim Lippard to use Signify.pm.
# Modified 20 November 2024 by Jim Lippard to get syslock group names from
#    signed file for plain and custom packages. For packages we assume
#    "etc" and "local" syslock group.
# Modified 12 December 2024 by Jim Lippard to use modern "open" syntax and
#    to change unveil to allow directory traversal which is likely the cause
#    of Signify failures due to unable to show grp files as readable.
# Modified 4 January 2025 by Jim Lippard to allow group files to be signed
#    with prior year's key (just as packages can be).
# Modified 29 January 2025 by Jim Lippard to get key name from host domain
#    name.
# Modified 4 February 2025 by Jim Lippard to make all system calls pass
#    argument lists instead of command line.
# Modified 10 February 2025 by Jim Lippard to not use syslock if not present
#    on system (in which case any signed grp files in the install dirs will
#    be ignored as extraneous files).
# Modified 30 July 2025 by Jim Lippard to allow options -f (to use
#    syslock/sysunlock even if system is not in single-user mode) and -n
#    (no syslock). -f does not call sysunlock (or syslock) with -f but
#    rather just makes the call on the assumption that the system is either
#    using uchg flags or the group(s) in question are uchg groups. If false,
#    error messages will be produced and it will abort, potentially with
#    some unlocking having already occurred.
# Modified 24 August 2025 by Jim Lippard to finally fix bug in adding
#    syslock groups caused by grep overriding the value of $_ from file
#    input.
# Modified 14 September 2025 by Jim Lippard to use OpenBSD MkTemp when
#    running on OpenBSD, use "install" for prefix on temp dir instead of
#    "distribute," add minimal pkg_add equivalent for non-OpenBSD systems
#    for some packages.
# Modified 15 September 2025 to correct creation of directory paths.

use strict;
use Archive::Tar;
use Cwd;
use File::Basename qw(fileparse basename);
use File::Path qw(rmtree make_path);
use Getopt::Std;
use IO::Uncompress::Gunzip;
use POSIX qw(strftime);
use Signify;
use Sys::Hostname;
use if $^O eq "openbsd", "OpenBSD::MkTemp", qw( mkdtemp );
use if $^O eq "openbsd", "OpenBSD::Pledge";
use if $^O eq "openbsd", "OpenBSD::Unveil";

### Constants.

my $INSTALL_DIR = '/var/install';

my @DEST_LOCATIONS = (
    '/etc',
    '/usr/local',
    '/home/_rsyncu/.ssh'
    );

my @SYSLOCK_GROUPS = (
    'etc',
    'local'
    );

my $MKTEMP = '/usr/bin/mktemp';
my $PKG_ADD = '/usr/sbin/pkg_add';
my $PWD = '/bin/pwd';
my $SIGNIFY = '/usr/bin/signify';
my $SYSCTL = '/usr/sbin/sysctl';
my $SYSLOCK = '/usr/local/bin/syslock';
my $SYSUNLOCK = '/usr/local/bin/sysunlock';
my $UNAME = '/usr/bin/uname';

my $CHANGELOG = '/etc/CHANGELOG';

my ($year) = (localtime (time()))[5];
$year += 1900;
my $prev_year = $year - 1;

my $HOSTNAME = hostname();
my (@HOSTNAME_ARRAY) = split (/\./, $HOSTNAME);
my $DOMAINNAME = pop (@HOSTNAME_ARRAY);
$DOMAINNAME = pop (@HOSTNAME_ARRAY) . '.' . $DOMAINNAME;

my $SIGNIFY_PUB_KEY_DIR = '/etc/signify';
my $SIGNIFY_KEY_NAME = "$DOMAINNAME-$year-pkg";
my $SIGNIFY_SEC_KEY = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NAME.sec";
my $SIGNIFY_PUB_KEY = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NAME.pub";
my $SIGNIFY_MIN_YEAR = $prev_year;
my $PRIOR_SIGNIFY_KEY_NAME = "$DOMAINNAME-$prev_year-pkg";
my $PRIOR_SIGNIFY_SEC_KEY = "$SIGNIFY_PUB_KEY_DIR/$PRIOR_SIGNIFY_KEY_NAME.sec";
my $PRIOR_SIGNIFY_PUB_KEY = "$SIGNIFY_PUB_KEY_DIR/$PRIOR_SIGNIFY_KEY_NAME.pub";
my $current_openbsd = `$UNAME -a`;
$current_openbsd =~ s/^OpenBSD [\w\.]+ (\d+)\.(\d+) .*$/$1$2/;
$current_openbsd--;
my $OPENBSD_MIN_VERSION = "$current_openbsd";

my $THREE_SPACES = '   ';

### Variables.

my ($securelevel, $host, $domain, $syslock_group, @files, $file,
    $user, $date, @changelog_entry, @contents, $line,
    $installed_something, $temp_dir);
my (@grp_files, @errors);
my %opts;
my $use_syslock = 1;
my $force_flag = 0;
my $debug_flag = 0;

### Main program.

# Install script:
# (run via rc.shutdown? but needs to be after securelevel changes)
# (could be during startup, but will need to add this script to the list
# of what has to be immutable to avoid security bypasses)
# 4. Securelevel check.
# 5. Look for packages.
# 6. Verify signature. signify -Vz -p /etc/signify/<domain>-<year>-pkg.pub
# 7. Change flags where necessary for contents (can use sysunlock).
# 8. Install. maybe verify again: signify -Vz -p /etc/signify/<domain>-<year>-pkg.pub | tar ztf - (use tar to install?)
# 9. Re-lock.
# 10. Update CHANGELOG.

# Check options.
getopts ('fnd', \%opts) || exit;

$force_flag = $opts{'f'};
$use_syslock = 0 if ($opts{'n'});
$debug_flag = $opts{'d'};

die "Cannot use -f and -n, they are mutually exclusive.\n" if ($force_flag & !$use_syslock);

if ($#ARGV != -1) {
    die "Usage: install.pl [-f (force)|-n (no syslock)|-d debug]\n";
}

# Get user.
$user = getpwuid($<);
die "Error. Must be run by root.\n" if ($user ne 'root');

# If no syslock, don't use syslock.
if (!-e $SYSLOCK) {
   $use_syslock = 0;
   die "Cannot use -f because you don't have syslock.\n" if ($force_flag);
}

# Check securelevel if using syslock (or -f force_flag is used).
if ($use_syslock && !$force_flag) {
    $securelevel = `$SYSCTL kern.securelevel`;
    chomp ($securelevel);
    if ($securelevel =~ /^.*=(\d+)$/) {
	$securelevel = $1;
	if ($securelevel != 0) {
	    die "Cannot unlock immutable files and directories for installation while system securelevel >=0. Securelevel: $securelevel.\n";
	}
    }
    else {
	die "Cannot get system securelevel. Output: $securelevel. $!\n";
    }
    print "DEBUG: securelevel=$securelevel\n" if ($debug_flag);
}

# Use pledge. Unveil somewhat limited since installations are going
# into significant places, but at least protects most system binaries
# and home directories. Will have to open up further if distribute.pl
# is used to install things in other locations.
if ($^O eq 'openbsd') {
    my $location_dir;
    pledge ('rpath', 'wpath', 'cpath', 'fattr', 'exec', 'proc', 'unveil') || die "Cannot pledge promises. $!\n";
    # Unveil /.
    unveil ('/', 'r');
    
    # Unveil for installation.
    foreach $location_dir (@DEST_LOCATIONS) {
	unveil ($location_dir, 'rwxc');
    }
    
    # Unveil commands used.
    # removed $MKTEMP.
    unveil ($PKG_ADD, 'rx');
    unveil ($PWD, 'rx'); # not sure what calls this
    unveil ($SIGNIFY, 'rx');
    unveil ($SYSCTL, 'rx');
    unveil ($SYSLOCK, 'rwxc') if ($use_syslock); # could update!
    unveil ($SYSUNLOCK, 'rwxc') if ($use_syslock); # could update!

    # Unveil signify pub key dir (could also update!)
    unveil ($SIGNIFY_PUB_KEY_DIR, 'rwc');

    # Unveil files modified.
    unveil ($INSTALL_DIR, "rwxc");
    unveil ($CHANGELOG, 'rwc');

    # Unveil /tmp.
    unveil ('/tmp', 'rwxc');

    # No more unveiling.
    unveil ();
}

$installed_something = 0;

# Check $INSTALL_DIR for contents; if any, then unlock.
# If not, say nothing to install.
# Ignore .sig signify files.
opendir (DIR, $INSTALL_DIR) || die "Cannot open $INSTALL_DIR to read files. $!\n";
@files = grep (!/^\.{1,2}$|\.sig$/, readdir (DIR));
closedir (DIR);

if ($use_syslock) {
    # Add any signed .grp files to syslock groups to unlock/lock.
    @grp_files = grep (/\.grp$/, @files);
    @files = grep (!/\.grp$/, @files);
    foreach $file (@grp_files) {
	if (!-e "$INSTALL_DIR/$file.sig") {
	    print "Warning: Install dir contains group file without signature. $file\n";
	}
	# If signature verifies, add syslock groups and remove sig file.
	else {
	    # Verify.
	    if (Signify::verify ("$INSTALL_DIR/$file", $SIGNIFY_PUB_KEY) ||
		Signify::verify ("$INSTALL_DIR/$file", $PRIOR_SIGNIFY_PUB_KEY)) {
		open (FILE, '<', "$INSTALL_DIR/$file") || die "Cannot open syslock group file. $! $INSTALL_DIR/$file\n";
		while (<FILE>) {
		    chomp;
		    my $group = $_; # grep overwrites $_ for its own ends
		    push (@SYSLOCK_GROUPS, $group) unless (grep (/^$group$/, @SYSLOCK_GROUPS));
		}
		close (FILE);
		print "DEBUG: syslock_groups = @SYSLOCK_GROUPS\n" if ($debug_flag);
	    }
	    else {
		@errors = Signify::signify_error;
		print "Bad signature on group file. $INSTALL_DIR/$file.sig @errors";
	    }
	    # Remove sig file.
	    unlink ("$INSTALL_DIR/$file.sig");
	}
	# Remove file.
	unlink ("$INSTALL_DIR/$file");
    }
} # use_syslock

die "Nothing to install.\n" if (!$files[0]);

# Get hostname.
$host = hostname();
($host, $domain) = split (/\./, $host, 2);

# Get date for CHANGELOG entry and get that started.
$date = strftime ("%Y-%m-%d", localtime (time()));
push (@changelog_entry, "$date-$user:");

# Unlock system.
if ($use_syslock) {
    foreach $syslock_group (@SYSLOCK_GROUPS) {
	print "DEBUG: unlocking syslock group $syslock_group\n" if ($debug_flag);
	system ($SYSUNLOCK, '-g', $syslock_group);
	if ($force_flag) {
	    my $exit_code = $? >> 8;
	    die "sysunlock failed with exit code: $exit_code\n" if ($exit_code != 0);
	}
    }
}

# Create temp dir. Needed only for signature verification.
if ($^O eq 'openbsd') {
    $temp_dir = mkdtemp ('/tmp/install.XXXXXXX');
}
else {
    $temp_dir = `$MKTEMP -d -q /tmp/install.XXXXXXX`;
    chomp ($temp_dir);
}

# For each file in the install dir:
# If it is of the form <host>-<date>-<time>-package.tgz:
#    Extract after verifying signature.
# If it is of the form <name>-<version>.tgz or <name>-<version>-no_xxx.tgz:
#    Install using pkg_add.
foreach $file (@files) {
    if ($file =~ /^$host-\d+-\d+-package\.tgz$/) {
	@contents = &verify_and_extract_package ("$INSTALL_DIR/$file");
	# Remove file and create CHANGELOG entry if successfully installed.
	if ($contents[0]) {
	    unlink ("$INSTALL_DIR/$file");
	    # Create CHANGELOG entry.
	    push (@changelog_entry, "\tInstalled package $file:");
	    foreach $line (@contents) {
		push (@changelog_entry, $line);
	    }

	    $installed_something = 1;
	}
    }
    elsif ($file =~ /^([\w\d-]+-[\d\.\w]+)\.tgz$/ || $file =~ /^([\w\d-]+-[\d\.\w]+-no_[0-9\w]+)\.tgz$/) {
	if (-d "$1") {
	    print "Package $file already installed per existence of directory /var/db/pkg/$1.\n";
	    unlink ("$INSTALL_DIR/$file");
	}
	# Remove file and create CHANGELOG entry if successfully installed.
	elsif (&install_pkg_add ("$INSTALL_DIR/$file")) {
	    unlink ("$INSTALL_DIR/$file");
	    
	    # Create CHANGELOG entry.
	    push (@changelog_entry, "\tUpgraded to $file.");

	    $installed_something = 1;
	}
    }
    else {
	print "Extraneous file in $INSTALL_DIR. Ignoring. $file\n";
    }
}

if ($use_syslock) {
    # Re-lock system.
    foreach $syslock_group (@SYSLOCK_GROUPS) {
	print "DEBUG: locking syslock group $syslock_group\n" if ($debug_flag);
	system ($SYSLOCK, '-g', $syslock_group);
    }
}

# Remove temp dir.
rmtree ($temp_dir);

# End if we didn't install anything.
if (!$installed_something) {
    print "Didn't find any files that could be installed.\n";
    exit;
}

# Update CHANGELOG.
open (FILE, '>>', $CHANGELOG) || die "Cannot open $CHANGELOG for appending. $!\n";
print FILE "\n";
foreach $line (@changelog_entry) {
    if (substr ($line, 0, 2) eq '\t') {
	$line = substr ($line, 2, length ($line) - 2);
	print FILE "\t$line\n";
    }
    else {
	print FILE "$line\n";
    }
}
close (FILE);

### Subroutines.

# Install a package with pkg_add.
# Should fail if not signed by a key in /etc/signify.
# (But there's a TRUSTED_PKG_PATH bypass...)
sub install_pkg_add {
    my ($file) = @_;

    if (!&verify_signature ($file)) {
	print "Invalid or missing signature. Could not install package $file.\n";
	return;
    }

    if ($^O ne 'openbsd' && !-e $PKG_ADD) {
	print "DEBUG: installing package $file with builtin minimal pkg_add.\n" if ($debug_flag);
	return 1 if (&minimal_pkg_add ($file)); # success
	return 0; # failure
    }

    print "DEBUG: installing package $file\n" if ($debug_flag);
    if (system ($PKG_ADD, $file)) {
	return 0; # failure (system returns nonzero for failure)
    }
    else {
	return 1; # success (system returns 0 for success)
    }
}

# Builtin minimal pkg_add, called after signature already verified.
# We verify signature after the tar file has been read to mitigate
# TOCTOU race and potential malicious archive substitution.
#   Look for +CONTENTS
#      See if it's for @arch *
#      Identify files to extract and dirs to create.
#      Create necessary dirs.
#      Extract files (including symlinks) into /usr/local
# Return 1 for success, 0 for failure.
sub minimal_pkg_add {
    my ($file) = @_;
    my ($tar, $file_minus_tgz, $content, @lines, $line,
	@files_to_extract, @dirs_to_create, $dir);
    my $DIR_PREFIX = '/usr/local';

    # Read package as Tar file.
    $tar = Archive::Tar->new;
    if (!$tar->read($file)) {
	print "Couldn't read tar file $file. $!\n";
	return 0;
    }
    
    # Do another signify verification post-tar-read to mitigate TOCTOU race.
    if (!&verify_signature ($file)) {
	print "Invalid or missing signature. Could not install package $file.\n";
	return;
    }

    $file_minus_tgz = basename ($file);
    $file_minus_tgz =~ s/\.tgz$//;

    # Get content of +CONTENTS file and validate.
    if ($content = $tar->get_content ('+CONTENTS')) {
	# Verify that it's got a PLIST comment and has a matching @name.
	if ($content !~ /^\@comment .OpenBSD: PLIST/m) {
	    print "No \"\@comment\" PLIST found in +CONTENTS file for $file.\n";
	    return 0;
	}
	if ($content !~ /^\@name $file_minus_tgz/m) {
	    print "No \"\@name $file_minus_tgz\" found in +CONTENTS file for $file.\n";
	    return 0;
	}

	# Verify it's for all architectures (e.g., perl script).
	if ($content !~ /^\@arch \*$/m) {
	    print "No \"\@arch *\" found in +CONTENTS file for $file.\n";
	    return 0;
	}

	# Verify it's intended for /usr/local.
	if ($content !~ /^\@cwd $DIR_PREFIX$/m) {
	    print "No \"\@cwd $DIR_PREFIX\" found in +CONTENTS file for $file.\n";
	    return 0;
	}
    }
    else {
	print "No +CONTENTS file found in $file.\n";
	return 0;
    }

    # Let's look for files and attempt some extraction.
    @lines = split (/\n/, $content);

    foreach $line (@lines) {
	if ($line !~ /^[\@\+]/) { # lines not beginning with @ or +
	    if ($line =~ /\/$/) { # lines ending in / are dirs
		push (@dirs_to_create, $line) unless (-e "$DIR_PREFIX/$dir");
	    }
	    else { # otherwise it's a file
		push (@files_to_extract, $line);
	    }
	}
    }

    # Set directory, packages extract to /usr/local.
    chdir ($DIR_PREFIX);
    $tar->setcwd ( cwd() );

    print "DEBUG: creating any required directories\n" if ($debug_flag);
    foreach $dir (@dirs_to_create) {
	if (!make_path ("$DIR_PREFIX/$dir")) {
	    print "Couldn't create required directory. $! $DIR_PREFIX/$dir\n";
	    return 0;
	}
	elsif ($debug_flag) {
	    print "DEBUG: created dir $dir (and any missing intermediates)\n";
	}
    }

    print "DEBUG: extracting package from tar file $file\n" if ($debug_flag);
    if ($tar->extract(@files_to_extract)) {
	return 1;
    }
    print "Couldn't extract files from package tar file $file\n" if ($debug_flag);
    return 0;
}

# Extract contents of a signed package and return the contents list.
sub verify_and_extract_package {
    my ($file) = @_;
    my ($tar, @fileobjs, $fileobj, $filedir, $filename);
    my (@output, $line);

    if (!&verify_signature ($file)) {
	print "Invalid or missing signature. Could not extract $file.\n";
	return;
    }

    # Now extract from file system root (/); previously using:
    #    system ($TAR, 'xfz', $file, '-C', '/');
    chdir ('/');
    $tar = Archive::Tar->new;
    if (!$tar->read($file)) {
	print "Couldn't read tar file $file. $!\n";
	return;
    }
    $tar->setcwd ( cwd() );
    print "DEBUG: extracting tar file $file\n" if ($debug_flag);
    @fileobjs = $tar->extract();
    
    # Indent each filename line with a tab, three spaces, and a leading slash.
    foreach $fileobj (@fileobjs) {
	$filedir = $fileobj->prefix;
	$filename = $fileobj->name;
	$line = '\t' . $THREE_SPACES . '/' . $filedir . '/' . $filename;
	push (@output, $line);
    }

    return (@output);
}

# Subroutine used in both distribute.pl and install.pl, be sure to keep
# consistent.
# Now uses Signify.pm to do most of the work.
sub verify_signature {
    my ($gzip_path) = @_;
    my ($signer, $signdate, @errors);
    my ($public_key, $signer_key_file, $signer_key_dir);
    my ($key_type, $num);

    # First, try with specific key.
    ($signer, $signdate) = Signify::verify_gzip ($gzip_path, $temp_dir,
						 "$SIGNIFY_KEY_NAME.pub",
						 $SIGNIFY_SEC_KEY);
    @errors = Signify::signify_error;
    # All good, signed by specific required key.
    if (!@errors) {
	return 1;
    }
    # Check for optional keys.
    # if pubkey is <domain>-(\d+)-pkg.pub and >= SIGNIFY_MIN_YEAR, it's
    # ok.  if it's openbsd-(\d+)-pkg.pub and >= OPENBSD_MIN_VERSION, it's ok
    elsif ($errors[0] =~ /public key is \"(.*)\" but/) {
	$public_key = $1;
	# public key for <domain> or openbsd
	if ($public_key =~ /^\Q$DOMAINNAME\E-\d+-pkg\.pub$|^openbsd-\d+-pkg\.pub$/) {
	    ($signer, $signdate) = Signify::verify_gzip ($gzip_path, $temp_dir);
	    @errors = Signify::signify_error;
	    # Didn't verify at all.
	    if (@errors) {
		print "@errors";
		return 0;
	    }
	    ($signer_key_file, $signer_key_dir) = fileparse ($signer);
	    if ($signer_key_dir ne $SIGNIFY_PUB_KEY_DIR) {
		print "Not signed by a key in $SIGNIFY_PUB_KEY_DIR, signed by $signer.\n";
		return 0;
	    }
	    # secret key for <domain> or openbsd
	    if ($signer_key_file =~ /^(\Q$DOMAINNAME\E)-(\d+)-pkg\.sec$|^(openbsd)-(\d+)-pkg\.sec$/) { 
		$key_type = $1;
		$num = $2;
		# Gotta meet minimum version requirements.
		if (($key_type eq $DOMAINNAME && $num >= $SIGNIFY_MIN_YEAR) ||
		    ($key_type eq 'openbsd' && $num >= $OPENBSD_MIN_VERSION)) {
		    return 1; # all good
		}
		# Didn't meet minimum version requirements
		else {
		    print "Not signed by required key version, signed by $signer.\n";
		    return 0;
		}
	    } # not secret key for <domain> or openbsd
	} # not public key for <domain> or openbsd
    }
    print "@errors";
    return 0;
}
