#!/usr/bin/perl
# Script to install signed packages created and distributed by distribute.pl.
#
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
# Modified 15 September 2025 by Jim Lippard to correct creation of directory paths.
# Modified 22 September 2025 by Jim Lippard to clean up some regexes.
# Modified 24 September 2025 by Jim Lippard to produce some output for success.
# Modified 2 October 2025 by Jim Lippard to correct check for already-installed
#    package and to make the minimal pkg_add equivalent create /var/db/pkg
#    registrations.
# Modified 3-4 October 2025 by Jim Lippard to add minimal pkg_delete
#    functionality for updating and removing old /var/db/pkg registrations,
#    install sample config file and use macos/linux version if available, don't
#    remove them if modified per file size or SHA256, fix bugs and test, set
#    timestamps and change gid for  minimal pkg_add, do some minimal file path
#    validation. Groundwork now allows for fairly simple creation of pkg_info
#    and pkg_check functionality (separate).
#    Ultimately the minimal pkg_add/pkg_delete should be separated out to its
#    own module that more fully parses the +CONTENTS file and maybe does some
#    dependency checking.
# Modified 10 November 2025 by Jim Lippard to unveil /dev/null for Signify.
# Modified 11 November 2025 by Jim Lippard to use /var/installation on macOS
#    because /var/install already exists and is protected. (No support in
#    distribute.pl for macOS destinations.) Use $PKG_DIR for /var/db/pkg,
#    create it before looking for prior package versions to delete if it
#    doesn't already exist.
# Modified 13 November 2025 by Jim Lippard to not allow OpenBSD signing
#    keys if not on OpenBSD.
# Modified 1 January 2026 by Jim Lippard to fix bug in verify_signature
#    when using secondary keys (pubkey dir no longer recorded).
# Modified 3 January 2026 by Jim Lippard to warn if next year's public
#    key hasn't shown up yet by two weeks before the new year.
# Modified 4 January 2026 by Jim Lippard to remove & from subroutine calls.
# Modified 25 February 2026 by Jim Lippard using Claude review, to fix
#    issues in the minimal_pkg_delete functionality and add some security
#    enhancements.
# Modified 9 April 2026 by Jim Lippard to use syslock's audit feature to
#    check if relevant groups are already unlocked when -f is used and
#    report if that's the case and the attempted sysunlock fails. There is
#    an edge case where you might have mixed uchg and schg with a group
#    used with install, where you previously could install into the uchg
#    components, which the audit will fail and the install will abort.
#    The right way to solve this is for install.pl to check specifically
#    to see if the files and directories where it need to install have
#    immutable flags set rather than relying on sysunlock -a. If you
#    encounter this problem you can explicitly reference group:uchg
#    in your distribute.conf, and only the uchg group will be unlocked
#    and audited. You can also set up arbitrary new groups for specific
#    installs, and use different configs in distribute.conf for the same
#    file installs if they are going into different environments.
# Modified 16 April 2026 by Claude at the direction of Jim Lippard to
#    support @mode setting in OpenBSD packages +CONTENTS files.
# Modified 20 April 2026 by Jim Lippard to fix version comparison typo.
# Modified 21 April 2026 by Jim Lippard to prompt for plain/custom files
#    signed with a key other than the <domain>-<year>-pkg format, but
#    to allow packages to be signed by any source for which there is
#    a public key in /etc/signify.
# Modified 2 May 2026 by Jim Lippard to check existence of public
#    keys, validate @mode settings, use File::Temp for non-OpenBSD
#    instead of direct call to mktemp, rename some variables and
#    restructure some code for clarity.
# Modified 4 May 2026 by Jim Lippard to remove etc as a default syslock
#    group (but keep it as a directory to unveil by default), fix some
#    non-fatal issues discovered after adding "use warnings", and check
#    for existence of syslock.conf, not just syslock binary. Change
#    version_gt subroutine to match distribute.pl.
# Modified 17 May 2026 by Jim Lippard to observe Linux and macOS
#    conventions on group for binary installations instead of imposing
#    OpenBSD conventions. Changed set_timestamp to set_timestamp_and_gid.
#    Changed behavior of syslock/sysunlock with new audit capabilities.
#    Main principle: unlock when necessary, re-lock groups we unlocked.
#    It doesn't necessarily leave things as they were before but it
#    leaves the groups we unlocked fully locked (even if they were
#    only partially locked when we started). Changed bareword filehandles
#    to $fh format.
# Modified 20 May 2026 by Jim Lippard to make second check in verify_signature
#    also fail fast and to simplify pre-install syslock audit checks by removing
#    the post-unlock audit check, quitting on failed sysunlock and cleaning up.
# Modified 6 June 2026 by Jim Lippard to add 'chown' pledge in addition to 'fattr'
#    which is necessary for root to chown files to a group it isn't a member of
#    (new in 7.9??).
# Modified 29 June 2026 by Jim Lippard to only print contents of +DISPLAY for
#    a package install if it's a new install or the contents have changed from
#    the previously installed version.
# Modified 30 June 2026 by Jim Lippard after Claude Opus 4.8 review to fix several bugs:
#    fixed +DISPLAY block (undeclared var, ->add typo), version_gt vN comparison (also
#    fixed in distribute.pl) macOS/@sample absolute-path dir creation, syslock re-lock
#    on die (END + signal handlers), regex metachar quoting, OpenBSD version-parse
#    fallback, and effective-UID privilege check.
use strict;
use warnings;
use Archive::Tar;
use Cwd;
use Fcntl ':mode'; # For S_ISREG
use File::Basename qw(fileparse basename dirname);
use File::Copy qw(copy);
use File::Path qw(rmtree make_path);
use if $^O ne 'openbsd', 'File::Temp', qw( :mktemp );
use Getopt::Std;
use IO::Uncompress::Gunzip;
use POSIX qw(strftime);
use Signify;
use Sys::Hostname;
use if $^O eq "openbsd", "OpenBSD::MkTemp", qw( mkdtemp );
use if $^O eq "openbsd", "OpenBSD::Pledge";
use if $^O eq "openbsd", "OpenBSD::Unveil";

if ($^O eq 'darwin' || $^O eq 'linux') {
    # hexdigest used for minimal_pkg_delete.
    require Digest::SHA;
}

### Constants.

my $VERSION = 'install.pl version 1.5 of 30 June 2026.';

my $INSTALL_DIR = '/var/install';
$INSTALL_DIR = '/var/installation' if ($^O eq 'darwin');

my $PKG_DIR = '/var/db/pkg';

my @DEST_LOCATIONS = (
    '/etc',
    '/usr/local',
    '/home/_rsyncu/.ssh'
    );

my @SYSLOCK_GROUPS = (
    'local'
    );

my $PKG_ADD = '/usr/sbin/pkg_add';
my $PWD = '/bin/pwd';
my $SIGNIFY = '/usr/bin/signify'; # used only for unveil, for Signify.pm
my $SYSCTL = '/usr/sbin/sysctl';
my $SYSLOCK = '/usr/local/bin/syslock';
my $SYSUNLOCK = '/usr/local/bin/sysunlock';
my $SYSLOCK_CONF = '/etc/syslock.conf';
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
my $next_year = $year + 1;
my $SIGNIFY_KEY_NAME_NEXT = "$DOMAINNAME-$next_year-pkg";
my $SIGNIFY_PUB_KEY_NEXT = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NAME_NEXT.pub";

my $current_openbsd;

if ($^O eq 'openbsd') {
    $current_openbsd = `$UNAME -a`;
    # Works so long as OpenBSD continues to use single-digit minor version numbers only.
    if ($current_openbsd =~ /^OpenBSD \S+ (\d+)\.(\d+) /) {
	$current_openbsd = "$1$2";
	$current_openbsd--;
    }
    else {
	chomp (my $u = $current_openbsd);
	die "Cannot identify current OpenBSD version from uname. $u\n";
    }   
}
else {
    $current_openbsd = 'not-openbsd';
}

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
getopts ('fndV', \%opts) || exit;

# -V version
if ($opts{'V'}) {
    print "$VERSION\n";
    exit 0;
}

$force_flag = $opts{'f'};
$use_syslock = 0 if ($opts{'n'});
$debug_flag = $opts{'d'};

die "Cannot use -f and -n, they are mutually exclusive.\n" if ($opts{'f'} && $opts{'n'});

if ($#ARGV != -1) {
    die "Usage: install.pl [-f (force)|-n (no syslock)|-V (version)|-d debug]\n";
}

# Set up signal handlers to force re-locking END block.
$SIG{INT} = $SIG{TERM} = sub { die "Caught SIG$_[0], aborting.\n" };

# Die if weird characters in domain name.
die "Invalid domain name: $DOMAINNAME\n" unless ($DOMAINNAME =~ /^[\w.-]+$/);

# Die if non-root
die "Error. Must be run by root.\n" if ($> != 0);

# username for the CHANGELOG entry, captured before pledge so we don't
# need the 'getpw' promise later
$user = getpwuid($>);

# If no syslock or config file, don't use syslock.
if (!-e $SYSLOCK || !-e $SYSLOCK_CONF) {
   $use_syslock = 0;
   die "Cannot use -f because you don't have syslock binary and config file.\n" if ($force_flag);
}

# Verify public key files exist.
unless (-r $SIGNIFY_PUB_KEY || -r $PRIOR_SIGNIFY_PUB_KEY) {
    die "Cannot find readable signify public keys.\n";
}

# Warn if next year's key hasn't shown up yet by two weeks before end of year.
my ($month, $day) = (localtime (time()))[4, 3];
$month++; # indexes are 0-11.
if ($month == 12 && $day > 16 && !-e $SIGNIFY_PUB_KEY_NEXT) {
    print "Warning: Next year's signing public key $SIGNIFY_PUB_KEY_NEXT isn't on this system.\n";
}

# Obtain securelevel if using syslock (but don't abort if -f force_flag is used).
if ($use_syslock && ($^O eq 'openbsd' || $^O eq 'darwin'|| $^O =~ /bsd$/)) {
    if (open (my $sysctl_fh, '-|', $SYSCTL, 'kern.securelevel')) {
	$securelevel = <$sysctl_fh>;
	close ($sysctl_fh);
	chomp ($securelevel);
	if ($^O eq 'darwin') {
	    $securelevel =~ s/kern\.securelevel:\s*(\d+)/$1/;
	}
	else {
	    $securelevel =~ s/kern\.securelevel\s*=\s*(\d+)/$1/;
	}
	if ($securelevel != 0 && !$force_flag) {
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
# 'chown' is needed in addition to 'fattr' just in case the tar
# extraction of a plain/custom file sets the group to one root isn't
# a member of.
if ($^O eq 'openbsd') {
    my $location_dir;
    pledge ('rpath', 'wpath', 'cpath', 'fattr', 'chown', 'exec', 'proc', 'unveil') || die "Cannot pledge promises. $!\n";
    # Unveil /.
    unveil ('/', 'r');
    
    # Unveil for installation.
    foreach $location_dir (@DEST_LOCATIONS) {
	unveil ($location_dir, 'rwxc');
    }
    
    # Unveil commands used.
    unveil ($PKG_ADD, 'rx');
    unveil ($PWD, 'rx'); # not sure what calls this
    unveil ($SIGNIFY, 'rx');
    unveil ($SYSCTL, 'rx');
    unveil ($SYSLOCK, 'rwxc') if ($use_syslock); # could update!
    unveil ($SYSUNLOCK, 'rwxc') if ($use_syslock); # could update!

    # Unveil signify pub key dir (could also update!)
    unveil ($SIGNIFY_PUB_KEY_DIR, 'rwc');
    # Unveil for Signify gzip verification.
    unveil ('/dev/null', 'rwc');

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
opendir (my $dir_fh, $INSTALL_DIR) || die "Cannot open $INSTALL_DIR to read files. $!\n";
@files = grep (!/^\.{1,2}$|\.sig$/, readdir ($dir_fh));
closedir ($dir_fh);

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
		open (my $fh, '<', "$INSTALL_DIR/$file") || die "Cannot open syslock group file. $! $INSTALL_DIR/$file\n";
		while (<$fh>) {
		    chomp;
		    my $group = $_; # grep overwrites $_ for its own ends
		    push (@SYSLOCK_GROUPS, $group) unless (grep { $_ eq $group } @SYSLOCK_GROUPS);
		}
		close ($fh);
		print "DEBUG: syslock_groups = @SYSLOCK_GROUPS\n" if ($debug_flag);
	    }
	    else {
		@errors = Signify::signify_error();
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
# Behavior: For each syslock group, check if unlocking is needed before doing
# so. Only unlock groups that have locked entries. Track which groups we
# unlock so we can re-lock only those at the end. When -f (force) is used
# at elevated securelevel (BSD/macOS only), we also pre-check for schg/sappnd
# locks that cannot be cleared, failing before any modification is made to
# avoid leaving the system in an asymmetric state. After installation,
# re-locking a group restores its configured state per syslock.conf - any
# pre-existing mixed-lock anomalies will be corrected to the configured
# state rather than preserved.
my %unlocked_by_us;

if ($use_syslock) {
    foreach $syslock_group (@SYSLOCK_GROUPS) {
        # Pre-check schg/sappnd locks - only meaningful on BSD/macOS at
        # elevated securelevel where these flags cannot be cleared.
        if ($force_flag && $^O ne 'linux' && $securelevel > 0) {
            # If group is an explicit :uchg or :uappnd, no schg/sappnd to worry about.
            unless ($syslock_group =~ /:uchg$|:uappnd$/) {
                # If untagged group or explicit :schg, check for locked schg members
                if ($syslock_group !~ /:sappnd$/) {
                    my $test_group = $syslock_group;
                    $test_group = $syslock_group . ':schg' if ($syslock_group !~ /:schg$/);
                    system ($SYSUNLOCK, '-g', $test_group, '-a', '-q');
                    my $schg_audit_code = $? >> 8;
                    if ($schg_audit_code != 0) {
                        die "Group $syslock_group has active schg locks that cannot be cleared at current securelevel. Aborting before modification.\n";
                    }
                }
                # If untagged group or explicit :sappnd, check for locked sappnd members
                if ($syslock_group !~ /:schg$/) {
                    my $test_group = $syslock_group;
                    $test_group = $syslock_group . ':sappnd' if ($syslock_group !~ /:sappnd$/);
                    system ($SYSUNLOCK, '-g', $test_group, '-a', '-q');
                    my $sappnd_audit_code = $? >> 8;
                    if ($sappnd_audit_code != 0) {
                        die "Group $syslock_group has active sappnd locks that cannot be cleared at current securelevel. Aborting before modification.\n";
                    }
                }
            }
        }
        
        # Check if unlock is needed at all. This is fast in the expected state
	# when everything is locked, but slow if everything or almost everything
	# is unlocked.
        system ($SYSUNLOCK, '-g', $syslock_group, '-a', '-o', '-q');
        my $needs_unlock = ($? >> 8) != 0;
        
        if ($needs_unlock) {
            print "DEBUG: unlocking syslock group $syslock_group\n" if ($debug_flag);
            system ($SYSUNLOCK, '-g', $syslock_group);
            my $unlock_exit_code = $? >> 8;

	    if ($unlock_exit_code != 0) {
		# Re-lock any groups we already unlocked before dying.
		relock_groups();
		die "Failed to unlock syslock group $syslock_group (exit: $unlock_exit_code).\n";
	    }
            $unlocked_by_us{$syslock_group} = 1;

	    # Skip post-check audit to verify unlock (previously only for
	    # BSD/macOS with securelevel > 0 where partial unlocks can happen.
	    # The potential race condition between the schg/sappnd checks above
	    # and the results of the unlock if another process is locking things
	    # in the group with schg wasn't solved by a post-unlock audit;
	    # sysunlock failure should give us a better result due to the slowness
	    # of the post-unlock audit that delayed the installation.
        }
    }
}

# Create temp dir. Needed for signature verification and for altering
# package +CONTENTS files for minimal_pkg_add.
$temp_dir = mkdtemp ('/tmp/install.XXXXXXX') || die "Could not create temp dir. $!\n";
chomp ($temp_dir);

# For each file in the install dir:
# If it is of the form <host>-<date>-<time>-package.tgz:
#    Extract after verifying signature.
# If it is of the form <name>-<version>.tgz or <name>-<version>-no_xxx.tgz:
#    Install using pkg_add.
foreach $file (@files) {
    if ($file =~ /^\Q$host\E-\d+-\d+-package\.tgz$/) {
	@contents = verify_and_extract_package ("$INSTALL_DIR/$file");
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
    elsif ($file =~ /^([\w\-]+-[\.\w]+)\.tgz$/ || $file =~ /^([\w\-]+-[\.\w]+-no_\w+)\.tgz$/) {
	if (-d "/var/db/pkg/$1") {
	    print "Package $file already installed per existence of directory /var/db/pkg/$1.\n";
	    unlink ("$INSTALL_DIR/$file");
	}
	# Remove file and create CHANGELOG entry if successfully installed.
	elsif (install_pkg_add ("$INSTALL_DIR/$file")) {
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

# Re-lock system. Only re-lock groups that we actually unlocked.
# Note: This restores the configured state per syslock.conf rather than
# the exact prior state. Any pre-existing partial-lock anomalies will be
# corrected to the configured state.
relock_groups () if ($use_syslock);

# Remove temp dir.
rmtree ($temp_dir);

# End if we didn't install anything.
if (!$installed_something) {
    print "Didn't find any files that could be installed.\n";
    exit;
}

# Update CHANGELOG.
open (my $fh, '>>', $CHANGELOG) || die "Cannot open $CHANGELOG for appending. $!\n";
print $fh "\n";
foreach $line (@changelog_entry) {
    print $fh "$line\n";
}
close ($fh);

### Subroutines.

# End block to ensure groups are relocked in cases where syslock dies while they're locked
# Signal handler for INT and TERM catches edge cases.
END {
    relock_groups() if ($use_syslock && %unlocked_by_us);
}

# Subroutine to relock syslock groups.
sub relock_groups {
    foreach my $syslock_group (@SYSLOCK_GROUPS) {
        if (delete $unlocked_by_us{$syslock_group}) { # delete makes this one-shot, calling twice is no-op
            print "DEBUG: re-locking syslock group $syslock_group\n" if ($debug_flag);
            system ($SYSLOCK, '-g', $syslock_group);
        }
#        else {
#            print "DEBUG: $syslock_group was already unlocked, not re-locking\n" if ($debug_flag);
#        }
    }
}

# Install a package with pkg_add.
# Should fail if not signed by a key in /etc/signify.
# (But there's a TRUSTED_PKG_PATH bypass...)
sub install_pkg_add {
    my ($file) = @_;

    if (!verify_signature ($file, 1)) { # 1 = is_package
	print "Invalid or missing signature. Could not install package $file.\n";
	return;
    }

    if ($^O ne 'openbsd' && !-e $PKG_ADD) {
	print "DEBUG: installing package $file with builtin minimal pkg_add.\n" if ($debug_flag);
	return 1 if (minimal_pkg_add ($file)); # success
	return 0; # failure
    }

    # Note: there is a TOCTOU race condition here because while OpenBSD's
    # pkg_add also checks for a signed package unless -D unsigned is
    # used (against /etc/signify keys), it will bypass the warning from
    # this script if it's not one of the expected signing keys.
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
    my ($tar, $file_minus_tgz, $content, @lines, $line, $last_file,
	@files_to_extract, @dirs_to_create, $file_extracted, %file_ts,
	$sample_file, $sample_source_file, %samples_to_extract,
	$dir, $older_package, %substitute_extract, $substitute_line,
	$substitute_file, $substitute_linux, $substitute_macos,
	%file_mode, %dir_mode, $current_mode);
    my $DIR_PREFIX = '/usr/local';
    
    # Default mode is 0755 (rwxr-xr-x)
    $current_mode = 0755;
    my $OPENBSD_PERL = 'libdata/perl5/site_perl';
    my $LINUX_PERL = 'lib/site_perl';
    my $PERLV = $^V;
    $PERLV =~ s/^v//;
    my $MACOS_PERL = "/Library/Perl/Updates/$PERLV";

    # Read package as Tar file.
    $tar = Archive::Tar->new;
    if (!$tar->read($file)) {
	print "Couldn't read tar file $file. $!\n";
	return 0;
    }
    
    # Do another signify verification post-tar-read to mitigate TOCTOU race.
    if (!verify_signature ($file, 1)) { # 1 = is_package
	print "Invalid or missing signature. Could not install package $file.\n";
	return 0;
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
	if ($content !~ /^\@name \Q$file_minus_tgz\E$/m) {
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

    if (!-e $PKG_DIR) {
	print "DEBUG: creating $PKG_DIR\n" if ($debug_flag);
	make_path ($PKG_DIR, { error => \my $err });
	if (@$err) {
	    print "Couldn't create $PKG_DIR. $!\n";
	    return 0; # didn't get to installation
	}
    }

    # Is a prior version of this package already installed? If so, remove it,
    # but don't touch @sample dirs and files unless the files are unchanged
    # since install.
    # (1) If older version of package is installed (check, need to use subrs
    #     from distribute.pl).)
    # (2) Read its +CONTENTS (should be subroutine that can also be used above?)
    # (3) Process in reverse (files to remove, directories to remove if empty,
    #     files to remove if unchanged, checking for custom installed configs
    #     for macOS/linux.
    my $old_pkg_display_hash;
    if ($older_package = older_package_installed ($file)) {
	if ($older_package =~ /^newer:(.*)$/) {
	    print "Newer package $1 already installed.\n";
	    return 0;
	}

	# Get +DISPLAY hash.
	$old_pkg_display_hash = get_pkg_display_hash ($older_package);
	
	print "DEBUG: deleting package $older_package with builtin minimal pkg_delete.\n" if ($debug_flag);
	if (!minimal_pkg_delete ($older_package)) {
	    print "Package delete of $older_package failed. Not installing $file.\n";
	    return 0;
	}
    }

    # Let's look for files and attempt some extraction.
    @lines = split (/\n/, $content);

    foreach $line (@lines) {
	if ($line !~ /^[\@\+]/) { # lines not beginning with @ or +
	    # Content lines are relative to @cwd (verified /usr/local above);
	    # an absolute path here is malformed. Reject before classifying.
	    # NB: the macOS /Library/Perl path is *derived* by the substitution
	    # below from a relative content line, so it never passes through here.
	    if ($line =~ m{^/}) {
		die "Aborting due to absolute path in $file +CONTENTS. $line\n";
	    }
	    if ($line =~ /\/$/ && valid_filepath ($line)) { # lines ending in / are dirs
		push (@dirs_to_create, $line) unless (-e "$DIR_PREFIX/$line");
		$dir_mode{$line} = $current_mode;
	    }
	    elsif (valid_filepath ($line)) { # otherwise it's a file
		$last_file = $line;
		$file_mode{$line} = $current_mode;
		if ($line =~ /^$OPENBSD_PERL/) {
		    $substitute_line = $line;
		    if ($^O eq 'linux') {
			$substitute_line =~ s/^$OPENBSD_PERL/$LINUX_PERL/;
			$substitute_linux = 1;
			push (@dirs_to_create, $LINUX_PERL) if (!-e "$DIR_PREFIX/$LINUX_PERL");
			$dir_mode{$LINUX_PERL} = $current_mode;
		    }
		    elsif ($^O eq 'darwin') {
			$substitute_line =~ s/^$OPENBSD_PERL/$MACOS_PERL/;
			$substitute_macos = 1;
			push (@dirs_to_create, $MACOS_PERL) if (!-e $MACOS_PERL);
			$dir_mode{$MACOS_PERL} = $current_mode;
		    }
		    $substitute_extract{$line} = $substitute_line;
		    $file_mode{$substitute_line} = $current_mode;
		}
		else {
		    push (@files_to_extract, $line);
		}
	    }
	    else {
		die "Aborting due to unusual line in $file +CONTENTS. $line\n";
	    }
	}
	# mode settings
	elsif ($line =~ /^\@mode\s+(\S+)$/) {
	    # Convert octal string to number
	    my $mode = oct($1);
	    # Reject setuid/setgid/sticky bits
	    if ($mode & 07000) {
		die "Aborting: special mode bits not allowed in \@mode: $1\n";
	    }
	    # Reject world-writeable
	    if ($mode & 0002) {
		die "Aborting: world-writeable mode not allowed: $1\n";
	    }
	    $current_mode = $mode;
	    print "DEBUG: setting mode to $1 (octal) = $current_mode (decimal)\n" if ($debug_flag);
	}
	# timestamps
	elsif ($line =~ /^\@ts (\d+)$/) {
	    $file_ts{$last_file} = $1;
	}
	elsif ($line =~ /^\@sample (.*)$/) {
	    $sample_file = $1;
	    if (!valid_filepath ($sample_file)) {
		die "Aborting due to unusual \@sample file path in $file +CONTENTS. $line\n";
	    }
	    # Trailing / is a dir to create, most likely in /etc.
	    if ($sample_file =~ /\/$/) {
		push (@dirs_to_create, $sample_file) unless (-e $sample_file);
		$dir_mode{$sample_file} = $current_mode;
	    }
	    # A file to extract into another location if not already present.
	    # Will typically be last file from @files_to_extract. Key is
	    # file in tar file, value is full path of destination.
	    else {
		$samples_to_extract{$last_file} = $sample_file;
		$file_mode{$sample_file} = $current_mode;
	    }
	}
    }

    # Set directory, packages extract to /usr/local.
    chdir ($DIR_PREFIX);
    $tar->setcwd ( cwd() );

    # Two cases where dirs to create are absolute paths: $MACOS_PERL and @sample dirs.
    print "DEBUG: creating any required directories\n" if ($debug_flag);
    print "DEBUG: \@dirs_to_create = @dirs_to_create\n" if ($debug_flag);
    foreach $dir (@dirs_to_create) {
	# Absolute paths (macOS perl modules under /Library/Perl, @sample dirs
	# under /etc) are used as-is; relative paths live under /usr/local.
	my $full_path = ($dir =~ m{^/}) ? $dir : "$DIR_PREFIX/$dir";
	make_path ($full_path, { error => \my $err });
	if (@$err) {
	    print "Couldn't create required directory. $! $full_path\n";
	    return 0;
	}
	elsif ($debug_flag) {
	    print "DEBUG: created dir $full_path (and any missing intermediates)\n";
	}
	
	# Set mode on directory if we have one recorded
	if (defined($dir_mode{$dir})) {
	    if (!chmod($dir_mode{$dir}, $full_path)) {
		print "DEBUG: could not set mode " . sprintf("%04o", $dir_mode{$dir}) . " on directory $full_path. $!\n" if ($debug_flag);
	    }
	    elsif ($debug_flag) {
		print "DEBUG: set mode " . sprintf("%04o", $dir_mode{$dir}) . " on directory $full_path\n";
	    }
	}
    }

    print "DEBUG: extracting package from tar file $file\n" if ($debug_flag);
    print "DEBUG: \@files_to_extract = @files_to_extract\n" if ($debug_flag);
    if ((@files_to_extract && $tar->extract (@files_to_extract)) ||
	$substitute_linux || $substitute_macos) {
	# Set timestamps and modes.
	foreach $file_extracted (@files_to_extract) {
	    set_timestamp_and_gid ("$DIR_PREFIX/$file_extracted", $file_ts{$file_extracted} // 0);
	    
	    # Set mode on file if we have one recorded
	    if (defined($file_mode{$file_extracted})) {
		my $full_path = "$DIR_PREFIX/$file_extracted";
		if (!chmod($file_mode{$file_extracted}, $full_path)) {
		    print "DEBUG: could not set mode " . sprintf("%04o", $file_mode{$file_extracted}) . " on file $full_path. $!\n" if ($debug_flag);
		}
		elsif ($debug_flag) {
		    print "DEBUG: set mode " . sprintf("%04o", $file_mode{$file_extracted}) . " on file $full_path\n";
		}
	    }
	}
	print "Installed package $file.\n";
	# Extract any perl modules. (This can occur when there are no
	# other files to extract.)
	if ($substitute_linux || $substitute_macos) {
	    print "DEBUG: extracting perl modules to alternate path\n" if ($debug_flag);
	    foreach $substitute_file (keys (%substitute_extract)) {
		print "DEBUG: extracting $substitute_file to $substitute_extract{$substitute_file}\n" if ($debug_flag);
		if (!$tar->extract_file ($substitute_file, $substitute_extract{$substitute_file})) {
		    print "DEBUG: could not extract $substitute_file to $substitute_extract{$substitute_file}. $!\n" if ($debug_flag);
		}
		else { # set timestamp, fix gid for Linux, and set mode
		    if ($substitute_linux) {
			set_timestamp_and_gid ("$DIR_PREFIX/$substitute_extract{$substitute_file}", $file_ts{$substitute_file} // 0);
			# Set mode on substituted file
			if (defined($file_mode{$substitute_line})) {
			    my $full_path = "$DIR_PREFIX/$substitute_extract{$substitute_file}";
			    if (!chmod($file_mode{$substitute_line}, $full_path)) {
				print "DEBUG: could not set mode " . sprintf("%04o", $file_mode{$substitute_line}) . " on file $full_path. $!\n" if ($debug_flag);
			    }
			    elsif ($debug_flag) {
				print "DEBUG: set mode " . sprintf("%04o", $file_mode{$substitute_line}) . " on file $full_path\n";
			    }
			}
		    }
		    if ($substitute_macos) {
			# already an absolute path for macOS.
			set_timestamp_and_gid ($substitute_extract{$substitute_file}, $file_ts{$substitute_file} // 0);
			# Set mode on substituted file
			if (defined($file_mode{$substitute_line})) {
			    my $full_path = $substitute_extract{$substitute_file};
			    if (!chmod($file_mode{$substitute_line}, $full_path)) {
				print "DEBUG: could not set mode " . sprintf("%04o", $file_mode{$substitute_line}) . " on file $full_path. $!\n" if ($debug_flag);
			    }
			    elsif ($debug_flag) {
				print "DEBUG: set mode " . sprintf("%04o", $file_mode{$substitute_line}) . " on file $full_path\n";
			    }
			}
		    }
		}
	    }
	}
	# Extract any sample files. (Assumption: never happens unless there
	# are other files to extract, otherwise this code won't be reached.)
	print "DEBUG: extracting sample files\n" if ($debug_flag);
	foreach my $tar_source (keys (%samples_to_extract)) {
	    if (!-e $samples_to_extract{$tar_source}) {
		$sample_source_file = $tar_source;

		# Look for custom config if on macOS or Linux.
		if ($^O eq 'darwin' || $^O eq 'linux') {
		    my ($sample_dir, $sample_base, $sample_prefix, $sample_check);
    
		    # Validate the source file path before manipulating it
		    if (!valid_filepath ($sample_source_file)) {
			print "Warning: Invalid sample source file path: $sample_source_file\n";
			next;  # or appropriate error handling
		    }
    
		    $sample_dir = dirname ($sample_source_file);
		    $sample_base = basename ($sample_source_file);
    
		    # Validate individual components
		    if ($sample_base =~ /\.\./ || $sample_base =~ /\//) {
			print "Warning: Invalid basename in sample file: $sample_base\n";
			next;
		    }
    
		    $sample_prefix = 'macos' if ($^O eq 'darwin');
		    $sample_prefix = 'linux' if ($^O eq 'linux');
    
		    # Construct path safely
		    $sample_check = $sample_dir . '/' . $sample_prefix . '.' . $sample_base;
    
		    # Validate constructed path
		    if (!valid_filepath ($sample_check)) {
			print "Warning: Constructed invalid path: $sample_check\n";
			next;
		    }
    
		    # Use eq instead of regex for matching
		    my $found = 0;
		    foreach my $check_file (@files_to_extract) {
			if ($check_file eq $sample_check) {
			    $found = 1;
			    last;
			}
		    }
		    $sample_source_file = $sample_check if ($found);
		}
		
		print "DEBUG: extracting sample file $sample_source_file\n" if ($debug_flag);
		$tar->extract_file ($sample_source_file, $samples_to_extract{$tar_source});
		# sample files are already an absolute path so no $DIR_PREFIX.
		set_timestamp_and_gid ($samples_to_extract{$tar_source}, $file_ts{$tar_source} // 0);
		
		# Set mode on sample file
		if (defined($file_mode{$samples_to_extract{$tar_source}})) {
		    my $full_path = $samples_to_extract{$tar_source};
		    if (!chmod($file_mode{$samples_to_extract{$tar_source}}, $full_path)) {
			print "DEBUG: could not set mode " . sprintf("%04o", $file_mode{$samples_to_extract{$tar_source}}) . " on sample file $full_path. $!\n" if ($debug_flag);
		    }
		    elsif ($debug_flag) {
			print "DEBUG: set mode " . sprintf("%04o", $file_mode{$samples_to_extract{$tar_source}}) . " on sample file $full_path\n";
		    }
		}
	    }
	    else {
		print "DEBUG: not extracting sample file $tar_source to already-existing $samples_to_extract{$tar_source}\n" if ($debug_flag);
	    }
	}
	
	# Register the installation.
	print "DEBUG: creating $PKG_DIR registration\n" if ($debug_flag);
	if (!make_path ("$PKG_DIR/$file_minus_tgz")) {
	    print "Couldn't create $PKG_DIR/$file_minus_tgz. $!\n";
	    return 1; # actual installation worked
	}
	# register package, ignoring errors
	$tar->extract_file('+CONTENTS', "$PKG_DIR/$file_minus_tgz/+CONTENTS");
	update_package_contents_file ("$PKG_DIR/$file_minus_tgz/+CONTENTS", $OPENBSD_PERL, $LINUX_PERL) if ($substitute_linux);
	update_package_contents_file ("$PKG_DIR/$file_minus_tgz/+CONTENTS", $OPENBSD_PERL, $MACOS_PERL) if ($substitute_macos);
	$tar->extract_file('+DESC', "$PKG_DIR/$file_minus_tgz/+DESC");
	if ($tar->contains_file('+DISPLAY')) {
	    $tar->extract_file('+DISPLAY', "$PKG_DIR/$file_minus_tgz/+DISPLAY");
	    my $new_pkg_display_content = $tar->get_content ('+DISPLAY');
	    my $new_pkg_display_hash;
	    if (defined $new_pkg_display_content) {
		my $ctx = Digest::SHA->new(256);
		$ctx->add ($new_pkg_display_content);
		$new_pkg_display_hash = $ctx->sha256_base64;
	    }
	    if (defined $new_pkg_display_hash &&
		(!defined $old_pkg_display_hash || $old_pkg_display_hash ne $new_pkg_display_hash)) {
		print $new_pkg_display_content;
	    }
	    elsif ($debug_flag) {
		print "DEBUG: +DISPLAY content matches old version. Suppressing output.\n";
	    }
	}
	return 1;
    }
    print "Couldn't extract files from package tar file $file\n" if ($debug_flag);
    return 0;
}

# Subroutine to determine if a string is a valid file path.
sub valid_filepath {
    my ($path) = @_;

    # no directory traversal
    return 0 if ($path =~ /\.\./);

    # reject paths with leading double-slashes or excessive slashes
    return 0 if ($path =~ /^\/\// || $path =~ /^\/{2,}/);

    # reject paths with null bytes
    return 0 if ($path =~ /\0/);

    # no odd characters (just alphanumeric, underscore, dot, slash, plus, at-sign, tilde, parens, space)
    # this covers all packages I have installed; only one has parens and a space.
    return 0 if ($path !~ /^[\w\-\.\/\+\@~\(\) ]+$/);

    return 1;
}

# Subroutine to set timestamps and fix gid.
sub set_timestamp_and_gid {
    my ($file, $timestamp) = @_;
    my ($atime);

    $atime = time();

    if ($timestamp == 0) {
	print "DEBUG: 0 timestamp for file $file\n" if ($debug_flag);
    }
    else {
	if (!utime ($atime, $timestamp, $file)) {
	    print "DEBUG: could not set timestamp $timestamp on file $file. $!\n" if ($debug_flag);
	}
    }

    if ($^O eq 'linux' || $^O eq 'darwin') {
	# Was using 'bin' on all platforms to follow the OpenBSD convention
	# (and fixing Linux here since bin is group 2 on Linux and 7 on
	# *BSD and macOS), but now just using local convention on each
	# platform. Packages are created on OpenBSD and use bin; we
	# change here to root for Linux and wheel for macOS which are both
	# 0.
	chown (-1, 0, $file);
    }
}

# Update package +CONTENTS file with altered paths for perl modules
# for Linux or macOS.  For macOS it's an absolute path and minimal_pkg_delete
# needs to make note of it.
sub update_package_contents_file {
    my ($file, $original, $substitution) = @_;

    if (open (my $fh, '<', $file)) { # open input +CONTENTS
	if (open (my $temp_fh, '>', "$temp_dir/+CONTENTS")) { # open temp +CONTENTS
	    while (<$fh>) {
		if (!/^[\@\+]/) {
		    if (/^$original/) {
			$_ =~ s/^$original/$substitution/;
		    }
		}
		print $temp_fh $_;
	    } # while
	    close ($fh);
	    close ($temp_fh);
	    copy ("$temp_dir/+CONTENTS", $file);
	    unlink ("$temp_dir/+CONTENTS");
	} # open temp +CONTENTS
    } # open input +CONTENTS
}

# Is an older version of a package installed?
sub older_package_installed {
    my ($file) = @_;
    my ($file_minus_tgz, $file_base, @files, $file_minus_version,
	$current_version, $no_suffix,
	$check_file, $check_version, $check_no_suffix);

    # Remove .tgz.
    $file_minus_tgz = $file;
    $file_minus_tgz =~ s/\.tgz$//;

    # Look at file basename (ignore dir).
    $file_base = basename ($file_minus_tgz);
    if ($file_base =~ /^(.*?)-(\d.*)$/) {
	$file_minus_version = $1;
	$current_version = $2;
	if ($current_version =~ /(-no_\w+)$/) {
	    $no_suffix = $1;
	    $current_version =~ s/-no_\w+$//;
	}
    }
    else {
	print "Couldn't parse version from $file_base.\n";
	return 0;
    }

    if (opendir ($dir_fh, $PKG_DIR)) {
	@files = grep (!/^\.{1,2}$/, readdir ($dir_fh));
	closedir ($dir_fh);
    }
    else {
	print "Cannot open dir $PKG_DIR. $!\n";
	return 0;
    }

    foreach $check_file (@files) {
	# Might have an older version here.
	if ($check_file =~ /^\Q$file_minus_version\E-(\d.*)$/) {
	    $check_version = $1;
	    if ($check_version =~ /^(.*)-(no_\w+)$/) {
		$check_no_suffix = $1;
		$check_version =~ s/-no_\w+$//;
		print "DEBUG: New package has $no_suffix, but current package has $check_no_suffix.\n" if ($no_suffix ne $check_no_suffix && $debug_flag);
		return 0;
	    }
	    elsif ($no_suffix) {
		print "DEBUG: New package has $no_suffix, but current package does not.\n" if ($debug_flag);
		return 0;
	    }
	    if (version_gt ($current_version, $check_version)) {
		return ($check_file);
	    }
	    elsif (version_gt ($check_version, $current_version)) {
		return ("newer:$check_file"); # newer version installed
	    }
	}
    }

    print "DEBUG: No older package found.\n" if ($debug_flag);
    return 0;
}

# Return file hash of existing package's +DISPLAY file, if it exists.
# (If I build more minimal_pkg functionality, the beginning of
# minimal_pkg_delete should be pulled out into a separate subroutine
# to obtain the +CONTENTS info, and get the file hash for this purpose
# from that location instead of computing it separately.
sub get_pkg_display_hash {
    my ($pkg) = @_;
    my $display_path = "$PKG_DIR/$pkg/+DISPLAY";

    return undef unless (-f $display_path && -r $display_path);

    if (open (my $fh, '<', $display_path)) {
        my $ctx = Digest::SHA->new(256);
        $ctx->addfile($fh);
        close ($fh);
        return $ctx->sha256_base64;
    }
    return undef;
}

# Delete a package.
sub minimal_pkg_delete {
    my ($file) = @_;
    my (@lines, $line, $last_file_to_delete, @dirs_to_delete, $dir_to_delete,
	@files_to_delete, $file_to_delete,
	$sample_file, $sample_source_file,
	%samples_to_delete, %sample_size, %sample_sha, %sample_ts,
	$ctx, $check_sha);
    my $DIR_PREFIX = '/usr/local';

    # Verify +CONTENTS file exists and is readable
    if (!-e "$PKG_DIR/$file/+CONTENTS") {
	print "Package registration not found: $PKG_DIR/$file/+CONTENTS\n";
	return 0;
    }
    
    if (!-r "$PKG_DIR/$file/+CONTENTS") {
	print "Cannot read package registration: $PKG_DIR/$file/+CONTENTS\n";
	return 0;
    }
    
    # Verify it's a regular file
    my @stat = stat("$PKG_DIR/$file/+CONTENTS");
    if (!@stat || !S_ISREG($stat[2])) {
	print "Package registration is not a regular file: $PKG_DIR/$file/+CONTENTS\n";
	return 0;
    }
    
    # OPTIONAL: Check if +CONTENTS has been modified recently (might indicate tampering)
    # This is a heuristic - legitimate operations might also modify it
    my $mtime = $stat[9];
    my $now = time();
    if (($now - $mtime) < 60) {  # Modified in last 60 seconds
	print "Warning: Package registration was recently modified: $PKG_DIR/$file/+CONTENTS\n";
	print "Proceeding anyway, but this might indicate tampering.\n";
    }

    # Read +CONTENTS, looking for dirs and files to delete and sample files
    # to potentially delete.
    open (my $fh, '<', "$PKG_DIR/$file/+CONTENTS");
    while (<$fh>) {
	chomp;
	if (!/^[\@\+]/) { # lines not beginning with @ or +
	    if (!valid_filepath ($_)) {
		print "Warning: Invalid filepath in +CONTENTS, skipping: $_\n";
		next;
	    }

	    # macOS puts perl modules into absolute path.
	    my $is_macos_perl_absolute = 0;
	    if ($^O eq 'darwin' && /^\/Library\/Perl\//) {
		$is_macos_perl_absolute = 1;
	    }
	    elsif (substr ($_, 0, 1) eq '/') {
		print "Warning: Rejecting absolute path in +CONTENTS: $_\n";
		next;
	    }
	    
	    if (/\/$/) { # lines ending in / are dirs
		if ($is_macos_perl_absolute) {
		    push (@dirs_to_delete, $_);
		}
		else {
		    push (@dirs_to_delete, "$DIR_PREFIX/$_");
		}
	    }
	    else { # otherwise it's a file
		if ($is_macos_perl_absolute) {
		    push (@files_to_delete, $_);
		}
		else {
		    push (@files_to_delete, "$DIR_PREFIX/$_");
		}
		$last_file_to_delete = $files_to_delete[-1];
	    }
	}
	# @sample is already a full path.
	elsif (/^\@sample (.*)$/) {
	    $sample_file = $1;

	    if (!valid_filepath ($sample_file)) {
		print "Warning: Invalid sample filepath in +CONTENTS, skipping: $sample_file\n";
		next;
	    }
	    
	    # Trailing / is a dir to delete, most likely in /etc.
	    if ($sample_file =~ /\/$/) {
		push (@dirs_to_delete, $sample_file) unless (!-e $sample_file);
	    }
	    # A file to extract into another location if not already present.
	    # Will typically be last file from @files_to_extract. Key is
	    # file in tar file, value is full path of destination.
	    else {
		if (defined ($last_file_to_delete)) {
		    $samples_to_delete{$last_file_to_delete} = $sample_file;
		}
	    }
	}
	# don't delete samples that have changed size/sha/ts.
	# don't delete non-empty dirs.
	elsif (/^\@size (\d+)$/) {
	    $sample_size{$last_file_to_delete} = $1 if (defined ($last_file_to_delete));
	}
	elsif (/^\@sha (.*)$/) {
	    $sample_sha{$last_file_to_delete} = $1 if (defined ($last_file_to_delete));
	}
	elsif (/^\@ts (.*)$/) {
	    $sample_ts{$last_file_to_delete} = $1 if (defined ($last_file_to_delete));
	}
	elsif (/^\@cwd (.*)$/) {
	    if ($1 ne $DIR_PREFIX) {
		print "+CONTENTS has \"\@cwd $1\", not /usr/local. Not removing package.\n";
		return 0;
	    }
	}
    }
    close ($fh);

    # Look for installed sample configs.
    foreach my $installed_file (keys (%samples_to_delete)) {
	if (-e $samples_to_delete{$installed_file}) {
	    $sample_source_file = $installed_file;

	    # Look for custom config if on macOS or Linux.
	    if ($^O eq 'darwin' || $^O eq 'linux') {
		my ($sample_dir, $sample_base, $sample_prefix, $sample_check);
    
		# Validate the source file path before manipulating it
		if (!valid_filepath($sample_source_file)) {
		    print "Warning: Invalid sample source file path: $sample_source_file\n";
		    next;  # or appropriate error handling
		}
    
		$sample_dir = dirname ($sample_source_file);
		$sample_base = basename ($sample_source_file);
    
		# Validate individual components
		if ($sample_base =~ /\.\./ || $sample_base =~ /\//) {
		    print "Warning: Invalid basename in sample file: $sample_base\n";
		    next;
		}
    
		$sample_prefix = 'macos' if ($^O eq 'darwin');
		$sample_prefix = 'linux' if ($^O eq 'linux');
    
		# Construct path safely
		$sample_check = $sample_dir . '/' . $sample_prefix . '.' . $sample_base;
    
		# Validate constructed path
		if (!valid_filepath($sample_check)) {
		    print "Warning: Constructed invalid path: $sample_check\n";
		    next;
		}
    
		# Use eq instead of regex for matching
		my $found = 0;
		foreach my $check_file (@files_to_delete) {
		    if ($check_file eq $sample_check) {
			$found = 1;
			last;
		    }
		}
		$sample_source_file = $sample_check if ($found);
	    }

	    # SECURITY FIX: check that it's unchanged against size/sha/ts of $sample_source_file
	    # Use file handle to avoid TOCTOU race condition
	    if (open (my $fh, '<', $samples_to_delete{$installed_file})) {
		# Get file stats while file is open
		my @stat = stat($fh);
		if (!@stat) {
		    print "DEBUG: could not stat file $samples_to_delete{$installed_file}. $!\n" if ($debug_flag);
		    close ($fh);
		    next;
		}
	    
		# Verify it's a regular file (not symlink, device, etc.)
		if (!S_ISREG($stat[2])) {
		    print "DEBUG: $samples_to_delete{$installed_file} is not a regular file, skipping.\n" if ($debug_flag);
		    close ($fh);
		    next;
		}
	    
		my $file_size = $stat[7];
		my $file_inode = $stat[1];
	    
		if ($file_size == $sample_size{$sample_source_file}) {
		    print "DEBUG: size of $samples_to_delete{$installed_file} unchanged from $sample_source_file.\n" if ($debug_flag);
		
		    # Compute SHA256 from file handle
		    $ctx = Digest::SHA->new(256);
		    $ctx->addfile($fh);
		    close ($fh);
		
		    $check_sha = $ctx->sha256_base64;
		    while (length($check_sha) % 4) { # manually add padding
			$check_sha .= '=';
		    }
		
		    if ($check_sha eq $sample_sha{$sample_source_file}) {
			# Verify file hasn't been replaced between close and unlink
			my @stat2 = stat($samples_to_delete{$installed_file});
			if (@stat2 && $stat2[1] == $file_inode && S_ISREG($stat2[2])) {
			    print "DEBUG: removing unchanged sample file $samples_to_delete{$installed_file}.\n" if ($debug_flag);
			    if (!unlink ($samples_to_delete{$installed_file})) {
				print "DEBUG: could not remove $samples_to_delete{$installed_file}. $!\n" if ($debug_flag);
			    }
			}
			else {
			    print "DEBUG: file $samples_to_delete{$installed_file} changed between check and delete, not removing.\n" if ($debug_flag);
			}
		    }
		    elsif ($debug_flag) {
			print "DEBUG: not removing changed (SHA256) sample file $samples_to_delete{$installed_file}.\n";
			print "DEBUG: current: $check_sha, original: $sample_sha{$sample_source_file}.\n";
		    }
		}
		else {
		    close ($fh);
		    print "DEBUG: not removing changed (size) sample file $samples_to_delete{$installed_file}.\n" if ($debug_flag);
		}
	    }
	    else {
		print "DEBUG: could not open file $samples_to_delete{$installed_file} to check. $!\n" if ($debug_flag);
	    }
	}
    }

    # delete files.
    foreach $file_to_delete (@files_to_delete) {
	print "DEBUG: removing $file_to_delete.\n" if ($debug_flag);
	# could check SHA256 before deletion, if so, should build a subroutine for it.
	if (!unlink ($file_to_delete)) {
	    print "DEBUG: could not remove $file_to_delete. $!\n" if ($debug_flag);
	}
    }

    # FIX: delete empty directories in reverse order (deepest first).
    # Reverse the array so we delete child directories before parents.
    @dirs_to_delete = reverse(@dirs_to_delete);

    # delete empty directories.
    foreach $dir_to_delete (@dirs_to_delete) {
	# delete if empty, ignore errors unless debug_flag is set.
	print "DEBUG: removing dir $dir_to_delete.\n" if ($debug_flag);
	if (!rmdir ($dir_to_delete)) {
	    	# Only print debug message if the error is not "Directory not empty"
	    # (we expect some dirs to not be empty, that's fine)
	    if ($debug_flag) {
		if ($! =~ /Directory not empty/i || $! =~ /ENOTEMPTY/) {
		    print "DEBUG: dir $dir_to_delete not empty, skipping. $!\n";
		}
		else {
		    print "DEBUG: could not remove dir $dir_to_delete. $!\n";
		}
	    }
	}
    }

    # FIX: Verify package directory only contains expected files before cleanup
    my @expected_files = ('+CONTENTS', '+DESC', '+DISPLAY');
    my @pkg_files;

    if (opendir(my $pkg_dh, "$PKG_DIR/$file")) {
	@pkg_files = grep { !/^\.\.?$/ } readdir($pkg_dh);
	closedir($pkg_dh);
    
	# Check for unexpected files
	my @unexpected;
	foreach my $pkg_file (@pkg_files) {
	    push(@unexpected, $pkg_file) unless (grep { $_ eq $pkg_file } @expected_files);
	}
    
	if (@unexpected) {
	    print "Warning: Unexpected files in package registration directory: @unexpected\n";
	    print "Package $file may not be fully removed. Manual cleanup of $PKG_DIR/$file may be required.\n";
	}
    }

    # Delete the package registration files
    my $cleanup_success = 1;

    if (-e "$PKG_DIR/$file/+CONTENTS") {
	if (!unlink ("$PKG_DIR/$file/+CONTENTS")) {
	    print "Could not remove package registration +CONTENTS. $!\n";
	    $cleanup_success = 0;
	}
    }

    if (-e "$PKG_DIR/$file/+DESC") {
	if (!unlink ("$PKG_DIR/$file/+DESC")) {
	    print "Could not remove package registration +DESC. $!\n";
	    $cleanup_success = 0;
	}
    }

    if (-e "$PKG_DIR/$file/+DISPLAY") {
	if (!unlink ("$PKG_DIR/$file/+DISPLAY")) {
	    print "Could not remove package registration +DISPLAY. $!\n";
	    $cleanup_success = 0;
	}
    }

    # Try to remove the directory
    if (!rmdir ("$PKG_DIR/$file")) {
	print "Could not remove package registration directory $PKG_DIR/$file. $!\n";
	return 0;
    }

    if (!$cleanup_success) {
	print "Warning: Some package registration files could not be removed, but directory cleanup succeeded.\n";
    }

    print "Deleted package $file.\n";
    return 1;
}

# Extract contents of a signed package and return the contents list.
sub verify_and_extract_package {
    my ($file) = @_;
    my ($tar, @fileobjs, $fileobj, $filedir, $filename);
    my (@output, $line);

    if (!verify_signature ($file, 0)) { # 0 = plain/custom
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
	$line = "\t" . $THREE_SPACES . '/' . $filedir . '/' . $filename;
	push (@output, $line);
    }

    return (@output);
}

# Prompt user to accept an alternate signing key.
sub should_accept_alternate_key {
    my ($found_key, $expected_key) = @_;
    
    print "\n";
    print "=" x 70 . "\n";
    print "SIGNATURE VERIFICATION WARNING\n";
    print "=" x 70 . "\n";
    print "File is signed with:  $found_key\n";
    print "Expected signing key: $expected_key\n";
    print "\n";
    print "The signing key is valid and in $SIGNIFY_PUB_KEY_DIR,\n";
    print "but it is not the expected key for this system.\n";
    print "\n";
    
    return yes_or_no("Accept this key and install the file? [y/n]: ");
}

### Following subroutines are present in both distribute.pl and install.pl
### and should be kept consistent.

## This subroutine is borrowed from sigtree.pl.
# Ask a yes or no question.
sub yes_or_no {
    my ($query) = @_;
    my ($answer);

    while (1) {
        print "$query";
        $answer = <STDIN>;
        chomp ($answer);

        if ($answer eq 'yes' || $answer eq 'y') {
            return 1;
        }
        elsif ($answer eq 'no' || $answer eq 'n') {
            return 0;
        }
        else {
            print "Please answer \"yes\" or \"no\".\n";
        }
    }
}

# Subroutine used in both distribute.pl and install.pl, be sure to keep
# consistent.
# Now uses Signify.pm to do most of the work.
sub verify_signature {
    my ($gzip_path, $is_package) = @_;
    my ($signer, $signdate, @errors);
    my ($public_key, $signer_key_file, $signer_key_dir);
    my ($key_type, $num);
    
    print "DEBUG: Verifying " . ($is_package ? "package" : "plain/custom") . ": $gzip_path\n" if ($debug_flag);

    ($signer, $signdate) = Signify::verify_gzip ($gzip_path, $temp_dir,
						 "$SIGNIFY_KEY_NAME.pub",
						 $SIGNIFY_SEC_KEY);
    @errors = Signify::signify_error;
    
    if (!@errors) {
	print "DEBUG: Verified with expected key: $SIGNIFY_KEY_NAME.sec\n" if ($debug_flag);
	return 1;
    }
    
    elsif ($errors[0] =~ /public key is \"(.*)\" but/) {
	(my $pubkey_dir, $public_key) = fileparse ($1); # $pubkey_dir ignored, no longer present anymore
	($signer, $signdate) = Signify::verify_gzip ($gzip_path, $temp_dir, $public_key);
	@errors = Signify::signify_error;
	
	if (@errors) {
	    print "@errors";
	    return 0;
	}
	
	($signer_key_file, $signer_key_dir) = fileparse ($signer);
	if ($signer_key_dir ne $SIGNIFY_PUB_KEY_DIR && $signer_key_dir ne './') {
	    print "Not signed by a key in $SIGNIFY_PUB_KEY_DIR, signed by $signer.\n";
	    return 0;
	}
	
	if ($is_package) {
	    if ($signer_key_file =~ /^([\w\.\-]+)-(\d+)-pkg\.sec$/) {
		$key_type = $1;
		$num = $2;
		if ($num >= $SIGNIFY_MIN_YEAR) {
		    print "DEBUG: Package signed with valid key: $signer_key_file\n" if ($debug_flag);
		    return 1;
		}
		else {
		    print "Package key $signer_key_file does not meet minimum year $SIGNIFY_MIN_YEAR.\n";
		    return 0;
		}
	    }
	    elsif ($^O eq 'openbsd' && $signer_key_file =~ /^(openbsd)-(\d+)-pkg\.sec$/) {
		$key_type = $1;
		$num = $2;
		if ($num >= $OPENBSD_MIN_VERSION) {
		    print "DEBUG: Package signed with OpenBSD key: $signer_key_file\n" if ($debug_flag);
		    return 1;
		}
		else {
		    print "OpenBSD key $signer_key_file does not meet minimum version.\n";
		    return 0;
		}
	    }
	    else {
		print "Package signed with unrecognized key pattern: $signer_key_file\n";
		return 0;
	    }
	}
	else {
	    if ($signer_key_file =~ /^(\Q$DOMAINNAME\E)-(\d+)-pkg\.sec$/) {
		$key_type = $1;
		$num = $2;
		if ($num >= $SIGNIFY_MIN_YEAR) {
		    print "DEBUG: Plain/custom signed with own domain key: $signer_key_file\n" if ($debug_flag);
		    return 1;
		}
		else {
		    print "Domain key $signer_key_file does not meet minimum year.\n";
		    return 0;
		}
	    }
	    # Plain/custom with non-domain key
	    else {
		# For any other key, check if we should accept it
		# In install.pl this prompts, in distribute.pl this rejects
		if (can_accept_alternate_plain_key($signer_key_file)) {
		    print "Accepted alternate signing key.\n";
		    return 1;
		}
		else {
		    print "Rejected alternate signing key.\n";
		    return 0;
		}
	    }
	}
    }
    
    print "@errors";
    return 0;
}

# This just returns 0 in distribute.pl.
sub can_accept_alternate_plain_key {
    my ($key_file) = @_;
    return should_accept_alternate_key ($key_file, "$SIGNIFY_KEY_NAME.sec");
}

# Subroutine used in both distribute.pl and install.pl, be sure to keep
# consistent.
# Returns 1 if $version1 > $version2.
sub version_gt {
    my ($version1, $version2) = @_;
    
    my ($v1_major, $v1_minor, $v1_patch, $v1_portrevision, $v1_vv) = version_parse ($version1);
    my ($v2_major, $v2_minor, $v2_patch, $v2_portrevision, $v2_vv) = version_parse ($version2);

    return 1 if ($v1_major > $v2_major);
    return 0 if ($v1_major < $v2_major);
    return 1 if ($v1_minor > $v2_minor);
    return 0 if ($v1_minor < $v2_minor);
    
    # Patch may be undef for maj.min(alpha)(pN) format
    if (defined($v1_patch) && defined($v2_patch)) {
        return 1 if ($v1_patch > $v2_patch);
        return 0 if ($v1_patch < $v2_patch);
    }
    
    # v_epoch can be either alpha (a-o) or epoch (vN)
    if (defined($v1_vv) || defined($v2_vv)) {
        my $e1 = $v1_vv // '';
        my $e2 = $v2_vv // '';

	my ($n1) = $e1 =~ /^v(\d+)$/;
	my ($n2) = $e2 =~ /^v(\d+)$/;

	# If both are epoch format (vN), compare numerically
	if (defined $n1 && defined $n2) {
	    return 1 if ($n1 > $n2);
	    return 0 if ($n1 < $n2);
	}
        # If both are alpha (single letters), string comparison works
        elsif ($e1 =~ /^[a-o]$/ && $e2 =~ /^[a-o]$/) {
            return 1 if ($e1 gt $e2);
            return 0 if ($e1 lt $e2);
        }
        # Mixed types - shouldn't happen for same package, but handle it
        else {
            return 1 if ($e1 gt $e2);
            return 0 if ($e1 lt $e2);
        }
    }
    
    # portrevision is always pN format
    if ($v1_portrevision =~ /^p(\d+)$/) {
        my $pr1 = $1;
        if ($v2_portrevision =~ /^p(\d+)$/) {
            my $pr2 = $1;
            return 1 if ($pr1 > $pr2);
            return 0 if ($pr1 < $pr2);
        }
        # v2 has no portrevision (set to -1), v1 has one
        return 1;
    }
    elsif ($v2_portrevision =~ /^p(\d+)$/) {
        # v1 has no portrevision, v2 does
        return 0;
    }
    
    return 0; # equal
}

# Subroutine used in both distribute.pl and install.pl, be sure to keep
# consistent.
# Parses versions.
# maj.min.pat(pN)(vN) (Many OpenBSD ports: 3.11.10p0, 9.20.8p0v3, 9.20.9v3)
# maj.min(alpha)(pN) (reportnew, py3-packaging)
# yyyy[.]mmdd(alpha)(pN)(vN) (rsync-tools, p5-Time-modules)
# maj.min.yyyymmdd(pN)(vN) (wireguard-tools)
# Doesn't support perl's vMAJOR.MINOR.PATcH
sub version_parse {
    my ($version) = @_;
    my ($major, $minor, $patch, $portrevision, $v_epoch);

    $portrevision = -1; # if not found

    # maj.min.pat(pN)(vN)
    if ($version =~ /^(\d+)\.(\d+)\.(\d+)(p\d+)?(v\d+)?$/) {
	$major = $1;
	$minor = $2;
	$patch = $3;
	$portrevision = $4 if (defined ($4));
	$v_epoch = $5 if (defined ($5));
    }
    # maj.min(alpha)(pN) (reportnew, py3-packaging)
    elsif ($version =~ /^(\d+)\.(\d+)([a-o])?(p\d+)?$/) {
	$major = $1;
	$minor = $2;
	$v_epoch = $3 if (defined ($3));
	$portrevision = $4 if (defined ($4));
    }
    # yyyy[.]mmdd(alpha)(pN)(vN) (rsync-tools, p5-Time-modules)
    elsif ($version =~ /^(\d{4})\.*(\d{2})(\d{2})([a-o]?)(p\d+)?(v\d+)?$/) {
	$major = $1;
	$minor = $2;
	$patch = $3;
	$v_epoch = $4 if (defined ($4)); # alpha
	$portrevision = $5 if (defined ($5));
	# alpha & vN - if really need both, should break out alpha?
	if (defined ($6) && defined ($v_epoch)) {
	    die "Cannot parse version \"$version\". Match on both an alpha patch and vN.\n";
	}
	# vN
	$v_epoch = $6 if (defined ($6));
    }
    # maj.min.yyyymmdd(pN)(vN) (wireguard-tools)
    elsif ($version =~ /^(\d+)\.(\d+)\.(\d{8})(p\d+)?(v\d+)?$/) {
	$major = $1;
	$minor = $2;
	$patch = $3;
	$portrevision = $4 if (defined ($4));
	$v_epoch = $5 if (defined ($5));
    }
    else {
	die "Cannot parse version \"$version\".\n";
    }

    return ($major, $minor, $patch, $portrevision, $v_epoch);
}
