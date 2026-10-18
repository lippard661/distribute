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
# Modified 2 July 2026 by Jim Lippard to fix +DISPLAY hash calculation (and same
#    issue for sample config file check).
# Modified 1 August 2026 by Jim Lippard to use /var/install/<hostname> as
#    source directory if present, to facilitate use of install.pl on the
#    same host where distribute.pl is used.
# Modified 16 September 2026 by Jim Lippard to gracefully handle one or two component
#    hostnames (as might be observed on macOS when not in home location) and allow
#    -k custom key specification. Remove requirement for PLIST comment in packages.
#    Allow common variable substitutions in @sample lines. Support @mode lines with
#    no mode specified (return to defaults), allow special mode bits.
# Modified 10 October 2026 by Jim Lippard after Claude review to close TOCTOU
#    windows by staging files from the install dir into the private temp dir
#    (O_NOFOLLOW, regular files only) and verifying/installing from the copy;
#    validate new package +CONTENTS before deleting the old package; fail
#    closed on unparseable securelevel (and treat -1 as insecure); preserve
#    exit status in END and remove temp dir there; warn loudly on re-lock
#    failure; catch SIGHUP; distinguish sysunlock run failures from audit
#    results and re-run failed audits verbosely; run all schg/sappnd
#    pre-checks before unlocking anything; expand pkg vars in @sample on
#    delete; fix perl module mode lookup and synthesized perl lib dir modes;
#    fix yyyy.mmdd+vN version parsing; check chdir; write CHANGELOG before
#    re-locking; reject paths in -k; validate .grp group names; require
#    /usr/bin/perl on macOS.
# Modified 15 October 2026 by Claude Opus 5.5 at the direction of Jim
#    Lippard (version 1.9): use Signify.pm 1.3's named-argument calls
#    (verify_gzip in verify_signature, the same change as distribute.pl,
#    and verify for .grp files) and require Signify.pm 1.3. Fix two
#    defects in verify_signature that made the fallback to a key other
#    than this year's always fail: fileparse's return values were taken
#    in the wrong order, so the second verification required a public
#    key named "./"; and a header key path in /etc/signify was compared
#    without fileparse's trailing slash. Packages signed with last year's
#    key, an OpenBSD key, or another <domain>-<year>-pkg key in
#    /etc/signify were refused since 1 January 2026. A plain/custom
#    package that stops extracting part way (an entry that cannot be
#    written) is now reported, recorded in CHANGELOG as partially
#    installed, left in place, and makes install.pl exit 1; previously the
#    files before the failing entry were installed silently and it said
#    nothing could be installed. unveil: no x on the install locations,
#    the install dir or /tmp (nothing is run from them), no unveil of
#    sysctl (run only before pledge); comments say why /dev/null and
#    /bin/pwd are unveiled.
# Modified 18 October 2026 by Claude Opus 5.5 at the direction of Jim
#    Lippard (version 1.9a): when an OpenBSD package that isn't already
#    installed is waiting, also unlock the groups in
#    @PACKAGE_SYSLOCK_GROUPS ("etcdir", for the /etc directory itself,
#    since pkg_add and @sample files can create or replace files directly
#    in /etc), but only if this host's syslock.conf defines them, so
#    distribute.pl need not send a .grp (and ask for a passphrase) for
#    packages. (The "etc" package default in the 20 November 2024 entry
#    was later removed; "local" is the only group unlocked for every
#    install.) An extraction that fails with EPERM now says the file or
#    its directory may still be immutable: Archive::Tar replaces a file by
#    unlinking and recreating it, so the directory must be unlocked too.
use strict;
use warnings;
use Archive::Tar;
use Cwd;
use Fcntl qw(:mode O_RDONLY O_NOFOLLOW O_NONBLOCK); # S_ISREG; flags for stage_file
use File::Basename qw(fileparse basename dirname);
use File::Copy qw(copy);
use File::Path qw(rmtree make_path);
use if $^O ne 'openbsd', 'File::Temp', qw( :mktemp );
use Getopt::Std;
use IO::Uncompress::Gunzip;
use POSIX qw(strftime);
# 1.3 or later: the named-argument calls below are read by older versions
# as positional arguments (a hash reference as the public key or temp dir).
use Signify 1.3;
use Sys::Hostname;
use if $^O eq "openbsd", "OpenBSD::MkTemp", qw( mkdtemp );
use if $^O eq "openbsd", "OpenBSD::Pledge";
use if $^O eq "openbsd", "OpenBSD::Unveil";

if ($^O eq 'darwin' || $^O eq 'linux') {
    # hexdigest used for minimal_pkg_delete.
    require Digest::SHA;
}

### Constants.

my $VERSION = 'install.pl version 1.9a of 18 October 2026.';

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

# Also unlocked when an OpenBSD package (not a plain/custom package) is
# waiting to be installed, if this host's syslock.conf defines the group:
# pkg_add, and the minimal pkg_add's @sample files, can create or replace
# files directly in /etc, which needs the /etc directory itself unlocked.
my @PACKAGE_SYSLOCK_GROUPS = (
    'etcdir'
    );

# OpenBSD package file names (with an optional -no_<flavor>), used by
# both the main loop and the check for @PACKAGE_SYSLOCK_GROUPS.
my $PKG_FILE_RE = qr/^([\w\-]+-[\.\w]+)\.tgz$/;
my $PKG_FLAVOR_FILE_RE = qr/^([\w\-]+-[\.\w]+-no_\w+)\.tgz$/;

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
my @HOSTNAME_ARRAY = split (/\./, $HOSTNAME);

my ($DOMAINNAME, $SHORT_HOSTNAME);

if (@HOSTNAME_ARRAY >= 3) {
    $DOMAINNAME = pop (@HOSTNAME_ARRAY);
    $DOMAINNAME = pop (@HOSTNAME_ARRAY) . '.' . $DOMAINNAME;
    $SHORT_HOSTNAME = shift (@HOSTNAME_ARRAY);
}
elsif (@HOSTNAME_ARRAY == 2) {
    $SHORT_HOSTNAME = $HOSTNAME_ARRAY[0];
    $DOMAINNAME = $HOSTNAME_ARRAY[1];
}
else {
    $SHORT_HOSTNAME = $HOSTNAME_ARRAY[0];
    $DOMAINNAME = '';  # will be overridden by -k if specified
}

# If the domain can't be determined, -k may supply it; without -k we die
# with that advice after option processing.

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

my %PKG_VARS = (
    'VARBASE'    => '/var',
    'PREFIX'     => '/usr/local',
    'LOCALBASE'  => '/usr/local',
    'SYSCONFDIR' => '/etc',
);

### Variables.

my ($securelevel, $host, $domain, $syslock_group, @files, $file,
    $user, $date, @changelog_entry, $line,
    $installed_something, $extract_failed, $temp_dir);
my (@grp_files, @errors);
my %opts;
my $custom_key_option;
my $debug_flag = 0;
my $force_flag = 0;
my $use_syslock = 1;

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
getopts ('dfk:nV', \%opts) || exit;

# -V version
if ($opts{'V'}) {
    print "$VERSION\n";
    exit 0;
}

$force_flag = $opts{'f'};
$custom_key_option = $opts{'k'};
$use_syslock = 0 if ($opts{'n'});
$debug_flag = $opts{'d'};

die "Cannot use -f and -n, they are mutually exclusive.\n" if ($opts{'f'} && $opts{'n'});

if ($#ARGV != -1) {
    die "Usage: install.pl [-f (force)|-k key|-n (no syslock)|-V (version)|-d debug]\n";
}

# On macOS, the perl module install path is derived from the version of the
# perl running this script ($^V). Our perl scripts use /usr/bin/perl, so
# running under another perl (e.g., Homebrew's, via "perl install.pl") would
# install modules where system perl never looks, and load a different
# Signify.pm.
die "On macOS install.pl must run under /usr/bin/perl (running $^X).\n"
    if ($^O eq 'darwin' && $^X !~ m{^/usr/bin/perl});

# Handle custom key option.
if ($custom_key_option) {
    my $custom_key_name = $custom_key_option;
    $custom_key_name =~ s/\.(pub|sec)$//;  # strip extension if given
    die "-k takes a key name in $SIGNIFY_PUB_KEY_DIR, not a path: $custom_key_option\n"
	if ($custom_key_name =~ m{/});

    my $custom_pub_key = "$SIGNIFY_PUB_KEY_DIR/$custom_key_name.pub";
    die "Custom public key not found: $custom_pub_key\n" unless (-r $custom_pub_key);
    
    # Override key variables
    $SIGNIFY_KEY_NAME = $custom_key_name;
    $SIGNIFY_PUB_KEY = $custom_pub_key;
    $SIGNIFY_SEC_KEY = "$SIGNIFY_PUB_KEY_DIR/$custom_key_name.sec";
    
    # Try to derive domain from key name for plain/custom file verification,
    # but don't require it - non-standard key names are accepted with a warning.
    if ($custom_key_name =~ /^([\w\.\-]+)-\d+-pkg$/) {
        $DOMAINNAME = $1;
        # Rebuild prior/next year key paths with new domain
        $PRIOR_SIGNIFY_KEY_NAME = "$DOMAINNAME-$prev_year-pkg";
        $PRIOR_SIGNIFY_SEC_KEY = "$SIGNIFY_PUB_KEY_DIR/$PRIOR_SIGNIFY_KEY_NAME.sec";
        $PRIOR_SIGNIFY_PUB_KEY = "$SIGNIFY_PUB_KEY_DIR/$PRIOR_SIGNIFY_KEY_NAME.pub";
        $SIGNIFY_KEY_NAME_NEXT = "$DOMAINNAME-$next_year-pkg";
        $SIGNIFY_PUB_KEY_NEXT = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NAME_NEXT.pub";
        print "DEBUG: Derived domain from key: $DOMAINNAME\n" if ($debug_flag);
    }
    else {
        print "Warning: key '$custom_key_name' doesn't follow domain-year-pkg pattern.\n";
        print "Plain/custom file verification will require user prompt for alternate keys.\n";
        # $DOMAINNAME left as hostname-derived (may be wrong on this network)
        # but that only affects plain/custom file auto-accept logic
    }
    
    print "DEBUG: Using custom key: $SIGNIFY_KEY_NAME\n" if ($debug_flag);
}
# Otherwise check domain name.
elsif (!$custom_key_option) {
    # No -k specified, domain was derived from hostname
    if (!$DOMAINNAME) {
        die "Cannot determine domain name from hostname '$HOSTNAME'. " .
            "Use -k to specify signing key explicitly.\n";
    }
    die "Invalid domain name: $DOMAINNAME\n" 
        unless ($DOMAINNAME =~ /^[\w.-]+$/);
}
# If -k was specified, domain either came from key name (good)
# or couldn't be derived (non-standard key, prompting will handle it)

# Always validate SHORT_HOSTNAME if we have one
die "Invalid host name: $SHORT_HOSTNAME\n" 
    if ($SHORT_HOSTNAME && $SHORT_HOSTNAME !~ /^[\w.-]+$/);

# Set up signal handlers to force re-locking END block. HUP matters for
# -f runs over ssh: a dropped session would otherwise kill us without
# running END, leaving unlocked groups unlocked.
$SIG{INT} = $SIG{TERM} = $SIG{HUP} = sub { die "Caught SIG$_[0], aborting.\n" };

# Die if non-root
die "Error. Must be run by root.\n" if ($> != 0);

# If /var/install/$SHORT_HOSTNAME exists, use it instead.
if (-d "$INSTALL_DIR/$SHORT_HOSTNAME") {
    $INSTALL_DIR .= '/' . $SHORT_HOSTNAME;
}

# Don't proceed if $INSTALL_DIR is a symlink.
die "Install dir must be a directory, but $INSTALL_DIR is a symlink. Cannot proceed.\n" if (-l $INSTALL_DIR);

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
# Fail closed: anything that isn't an integer is an error, not securelevel 0.
# -1 (permanently insecure) and 0 (insecure) both allow clearing schg/sappnd.
if ($use_syslock && ($^O eq 'openbsd' || $^O eq 'darwin'|| $^O =~ /bsd$/)) {
    if (open (my $sysctl_fh, '-|', $SYSCTL, '-n', 'kern.securelevel')) {
	my $sysctl_out = <$sysctl_fh>;
	close ($sysctl_fh);
	$sysctl_out = '' unless (defined ($sysctl_out));
	chomp ($sysctl_out);
	die "Unexpected kern.securelevel output from $SYSCTL: '$sysctl_out'\n"
	    unless ($sysctl_out =~ /^-?\d+$/);
	$securelevel = $sysctl_out;
	if ($securelevel > 0 && !$force_flag) {
	    die "Cannot unlock immutable files and directories for installation while system securelevel > 0. Securelevel: $securelevel.\n";
	}
    }
    else {
	die "Cannot run $SYSCTL to get system securelevel. $!\n";
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
    
    # Unveil for installation. No 'x': unveil's x is checked only when
    # execve(2) names a path, nothing is run from these trees except
    # syslock/sysunlock (unveiled below), and pkg_add, once exec'd, runs
    # without our pledge and unveil.
    foreach $location_dir (@DEST_LOCATIONS) {
	unveil ($location_dir, 'rwc');
    }
    
    # Unveil commands used after this point. (sysctl and uname run only
    # before pledge, so they need no unveil.)
    unveil ($PKG_ADD, 'rx');
    unveil ($PWD, 'rx'); # Cwd::cwd() runs /bin/pwd (Archive::Tar setcwd)
    unveil ($SIGNIFY, 'rx');
    unveil ($SYSLOCK, 'rwxc') if ($use_syslock); # could update!
    unveil ($SYSUNLOCK, 'rwxc') if ($use_syslock); # could update!

    # Unveil signify pub key dir (could also update!)
    unveil ($SIGNIFY_PUB_KEY_DIR, 'rwc');
    # For Signify gzip verification: its forked child opens /dev/null for
    # writing with open(2). Since OpenBSD 7.9 only libc's __pledge_open(2)
    # bypasses unveil for /dev/null, so this unveil is required ('c'
    # because '>' opens with O_CREAT).
    unveil ('/dev/null', 'rwc');

    # Unveil files modified.
    unveil ($INSTALL_DIR, 'rwc');
    unveil ($CHANGELOG, 'rwc');

    # Unveil /tmp (staging and temp files; nothing is run from it).
    unveil ('/tmp', 'rwc');

    # No more unveiling.
    unveil ();
}

# Create temp dir. Created early because files from $INSTALL_DIR (which
# other accounts can write to) are staged into it before verification, and
# it's also used for signature verification and for altering package
# +CONTENTS files for minimal_pkg_add. mkdtemp creates it mode 0700.
$temp_dir = mkdtemp ('/tmp/install.XXXXXXX') || die "Could not create temp dir. $!\n";
chomp ($temp_dir);

$installed_something = 0;

# Check $INSTALL_DIR for contents; if any, then unlock.
# If not, say nothing to install.
# Ignore .sig signify files.
opendir (my $dir_fh, $INSTALL_DIR) || die "Cannot open $INSTALL_DIR to read files. $!\n";
@files = grep (!/^\.{1,2}$|\.sig$/, readdir ($dir_fh));
closedir ($dir_fh);

if ($use_syslock) {
    # Add any signed .grp files to syslock groups to unlock/lock.
    # The group file and its signature are staged into the private temp dir
    # first, so the copy we verify is the copy we read.
    @grp_files = grep (/\.grp$/, @files);
    @files = grep (!/\.grp$/, @files);
    foreach $file (@grp_files) {
	if (!-e "$INSTALL_DIR/$file.sig") {
	    print "Warning: Install dir contains group file without signature. $file\n";
	}
	# If signature verifies, add syslock groups and remove sig file.
	else {
	    my $staged_grp = stage_file ("$INSTALL_DIR/$file");
	    my $staged_sig = stage_file ("$INSTALL_DIR/$file.sig");
	    # Verify.
	    if ($staged_grp && $staged_sig &&
		(Signify::verify ($staged_grp, { public_key_path => $SIGNIFY_PUB_KEY }) ||
		 Signify::verify ($staged_grp, { public_key_path => $PRIOR_SIGNIFY_PUB_KEY }))) {
		open (my $fh, '<', $staged_grp) || die "Cannot open syslock group file. $! $staged_grp\n";
		while (<$fh>) {
		    chomp;
		    my $group = $_; # grep overwrites $_ for its own ends
		    next if ($group eq '');
		    die "Invalid syslock group name \"$group\" in group file $file.\n"
			unless ($group =~ /^[\w.-]+(?::[su](?:chg|appnd))?$/);
		    push (@SYSLOCK_GROUPS, $group) unless (grep { $_ eq $group } @SYSLOCK_GROUPS);
		}
		close ($fh);
		print "DEBUG: syslock_groups = @SYSLOCK_GROUPS\n" if ($debug_flag);
	    }
	    elsif ($staged_grp && $staged_sig) {
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

# Add @PACKAGE_SYSLOCK_GROUPS if a package that isn't already installed is
# waiting. Only groups this host's syslock.conf defines: syslock dies on an
# unknown group, which would abort the install (hosts without one, such as
# some Linux and macOS hosts, are skipped).
if ($use_syslock && grep { package_pending ($_) } @files) {
    my %defined = syslock_conf_groups ();
    foreach my $group (@PACKAGE_SYSLOCK_GROUPS) {
	if (!$defined{$group}) {
	    print "DEBUG: package group $group not defined in $SYSLOCK_CONF, not unlocking it\n" if ($debug_flag);
	    next;
	}
	push (@SYSLOCK_GROUPS, $group) unless (grep { $_ eq $group } @SYSLOCK_GROUPS);
    }
    print "DEBUG: syslock_groups = @SYSLOCK_GROUPS\n" if ($debug_flag);
}

# Get date for CHANGELOG entry and get that started.
$date = strftime ("%Y-%m-%d", localtime (time()));
push (@changelog_entry, "$date-$user:");

# Unlock system.
# Behavior: For each syslock group, check if unlocking is needed before doing
# so. Only unlock groups that have locked entries. Track which groups we
# unlock so we can re-lock only those at the end. When -f (force) is used
# at elevated securelevel (BSD/macOS only), we first pre-check ALL groups for
# schg/sappnd locks that cannot be cleared, failing before any group is
# modified to avoid leaving the system in an asymmetric state. After
# installation, re-locking a group restores its configured state per
# syslock.conf - any pre-existing mixed-lock anomalies will be corrected to
# the configured state rather than preserved.
my %unlocked_by_us;

if ($use_syslock) {
    # Pass 1: pre-check schg/sappnd locks - only meaningful on BSD/macOS at
    # elevated securelevel where these flags cannot be cleared.
    if ($force_flag && $^O ne 'linux' && $securelevel > 0) {
	foreach $syslock_group (@SYSLOCK_GROUPS) {
	    # If group is an explicit :uchg or :uappnd, no schg/sappnd to worry about.
	    next if ($syslock_group =~ /:uchg$|:uappnd$/);
	    my @test_types;
	    # Untagged group or explicit :schg -> check schg members;
	    # untagged group or explicit :sappnd -> check sappnd members.
	    push (@test_types, 'schg') if ($syslock_group !~ /:sappnd$/);
	    push (@test_types, 'sappnd') if ($syslock_group !~ /:schg$/);
	    foreach my $type (@test_types) {
		my $test_group = $syslock_group;
		$test_group .= ":$type" if ($syslock_group !~ /:\Q$type\E$/);
		my $audit_code = run_sysunlock ('-g', $test_group, '-a', '-q');
		if ($audit_code != 0) {
		    # Re-run without -q so the output shows what was found
		    # (or what went wrong) rather than leaving it a mystery.
		    print "Audit of syslock group $test_group returned exit code $audit_code; re-running without -q:\n";
		    run_sysunlock ('-g', $test_group, '-a');
		    die "Group $syslock_group has $type-locked files that cannot be cleared at securelevel $securelevel, or the audit itself failed (exit $audit_code; see output above). Aborting before modification.\n";
		}
	    }
	}
    }

    # Pass 2: unlock groups that need it.
    foreach $syslock_group (@SYSLOCK_GROUPS) {
        # Check if unlock is needed at all. This is fast in the expected state
	# when everything is locked, but slow if everything or almost everything
	# is unlocked.
        my $needs_unlock = (run_sysunlock ('-g', $syslock_group, '-a', '-o', '-q') != 0);

        if ($needs_unlock) {
            print "DEBUG: unlocking syslock group $syslock_group\n" if ($debug_flag);
            my $unlock_exit_code = run_sysunlock ('-g', $syslock_group);

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
	else {
	    print "DEBUG: $syslock_group already unlocked, skipping\n" if ($debug_flag);
	}
    }
}

# For each file in the install dir:
# If it is of the form <host>-<date>-<time>-package.tgz:
#    Extract after verifying signature.
# If it is of the form <name>-<version>.tgz or <name>-<version>-no_xxx.tgz:
#    Install using pkg_add.
# Each file is first staged into the private temp dir; signature
# verification and installation both use the staged copy, so a file
# replaced in $INSTALL_DIR mid-run can't be substituted after verification.
foreach $file (@files) {
    if ($file =~ /^\Q$host\E-\d+-\d+-package\.tgz$/) {
	my $staged = stage_file ("$INSTALL_DIR/$file");
	next unless ($staged);
	my ($extracted, $extract_error) = verify_and_extract_package ($staged);
	# Remove file and create CHANGELOG entry if successfully installed.
	if (defined ($extracted) && !defined ($extract_error) && @$extracted) {
	    unlink ("$INSTALL_DIR/$file");
	    # Create CHANGELOG entry.
	    push (@changelog_entry, "\tInstalled package $file:");
	    foreach $line (@$extracted) {
		push (@changelog_entry, $line);
	    }

	    $installed_something = 1;
	}
	elsif (defined ($extract_error)) {
	    # Archive::Tar stops at the first entry it cannot write, after
	    # writing every entry before it. Record what did change, and
	    # leave the package in place so it can be retried.
	    $extract_failed = 1;
	    print "ERROR: extraction of $file stopped part way: $extract_error\n";
	    print "ERROR: $file left in $INSTALL_DIR; " .
		(@$extracted ? scalar (@$extracted) . " earlier file(s) from it were installed.\n"
		 : "nothing from it was installed.\n");
	    if (@$extracted) {
		push (@changelog_entry, "\tPARTIALLY installed package $file (stopped: $extract_error):");
		foreach $line (@$extracted) {
		    push (@changelog_entry, $line);
		}
		$installed_something = 1;
	    }
	}
    }
    elsif ($file =~ $PKG_FILE_RE || $file =~ $PKG_FLAVOR_FILE_RE) {
	my $pkg_name = $1;
	if (-d "/var/db/pkg/$pkg_name") {
	    print "Package $file already installed per existence of directory /var/db/pkg/$pkg_name.\n";
	    unlink ("$INSTALL_DIR/$file");
	}
	else {
	    my $staged = stage_file ("$INSTALL_DIR/$file");
	    # Remove file and create CHANGELOG entry if successfully installed.
	    if ($staged && install_pkg_add ($staged)) {
		unlink ("$INSTALL_DIR/$file");

		# Create CHANGELOG entry.
		push (@changelog_entry, "\tUpgraded to $file.");

		$installed_something = 1;
	    }
	}
    }
    else {
	print "Extraneous file in $INSTALL_DIR. Ignoring. $file\n";
    }
}

# Update CHANGELOG before re-locking, in case it is ever placed in a
# syslock group that we unlocked.
if ($installed_something) {
    open (my $fh, '>>', $CHANGELOG) || die "Cannot open $CHANGELOG for appending. $!\n";
    print $fh "\n";
    foreach $line (@changelog_entry) {
	print $fh "$line\n";
    }
    close ($fh);
}

# Re-lock system. Only re-lock groups that we actually unlocked.
# Note: This restores the configured state per syslock.conf rather than
# the exact prior state. Any pre-existing partial-lock anomalies will be
# corrected to the configured state.
relock_groups () if ($use_syslock);

# Remove temp dir (and the staged copies in it).
rmtree ($temp_dir);

# End if we didn't install anything.
if (!$installed_something) {
    if ($extract_failed) {
	print "Nothing was installed (see errors above).\n";
	exit 1;
    }
    print "Didn't find any files that could be installed.\n";
    exit;
}

# A package that stopped part way leaves the system in a mixed state.
exit 1 if ($extract_failed);

### Subroutines.

# End block to ensure groups are relocked in cases where we die while they're
# unlocked. Signal handlers for INT, TERM, and HUP catch edge cases.
# "local $?" is required: system() inside END would otherwise overwrite the
# exit status, making a failed run (die) exit 0.
END {
    local $?;
    relock_groups() if ($use_syslock && %unlocked_by_us);
    rmtree ($temp_dir) if (defined ($temp_dir) && -d $temp_dir);
}

# True if $file is an OpenBSD package (not this host's plain/custom
# package) that the main loop would install: same patterns, and not
# already registered in /var/db/pkg.
sub package_pending {
    my ($file) = @_;
    return 0 if ($file =~ /^\Q$host\E-\d+-\d+-package\.tgz$/);
    return 0 unless ($file =~ $PKG_FILE_RE || $file =~ $PKG_FLAVOR_FILE_RE);
    return (!-d "/var/db/pkg/$1");
}

# Group names defined by "group:" lines in syslock.conf (the same line
# syntax syslock parses; a trailing "# comment" is ignored).
sub syslock_conf_groups {
    my %groups;
    open (my $fh, '<', $SYSLOCK_CONF) || return %groups;
    while (my $line = <$fh>) {
	next unless ($line =~ /^group:\s+(.*)$/);
	(my $names = $1) =~ s/#.*//;
	$groups{$_} = 1 foreach (split (' ', $names));
    }
    close ($fh);
    return %groups;
}

# Subroutine to relock syslock groups. A failed re-lock is reported loudly,
# since it can leave files unlocked.
sub relock_groups {
    foreach my $syslock_group (@SYSLOCK_GROUPS) {
        if (delete $unlocked_by_us{$syslock_group}) { # delete makes this one-shot, calling twice is no-op
            print "DEBUG: re-locking syslock group $syslock_group\n" if ($debug_flag);
            system ($SYSLOCK, '-g', $syslock_group);
	    if ($? != 0) {
		my $why = ($? == -1) ? "could not run $SYSLOCK: $!"
		    : ($? & 127) ? 'killed by signal ' . ($? & 127)
		    : 'exit ' . ($? >> 8);
		print STDERR "WARNING: re-lock of syslock group $syslock_group FAILED ($why).\n";
		print STDERR "WARNING: files may be left unlocked; run '$SYSLOCK -g $syslock_group' manually.\n";
	    }
        }
    }
}

# Run sysunlock with the given arguments and return its exit code. Dies if
# sysunlock couldn't be run or was killed by a signal, so that "couldn't run
# the audit" is never mistaken for "the audit found locked files" (with $?
# == -1, $? >> 8 is a huge nonzero number).
sub run_sysunlock {
    my (@args) = @_;
    system ($SYSUNLOCK, @args);
    die "Could not run $SYSUNLOCK @args: $!\n" if ($? == -1);
    die "$SYSUNLOCK @args killed by signal " . ($? & 127) . "\n" if ($? & 127);
    return ($? >> 8);
}

# Copy a file from $INSTALL_DIR (writable by other accounts) into the
# private temp dir, refusing symlinks and anything that isn't a regular
# file (O_NONBLOCK keeps a FIFO from hanging the open). Returns the staged
# path, which keeps the original basename, or undef.
sub stage_file {
    my ($src) = @_;
    my $in;

    if (!sysopen ($in, $src, O_RDONLY | O_NOFOLLOW | O_NONBLOCK)) {
	# O_NOFOLLOW on a symlink fails with ELOOP.
	print "Skipping $src: " . ($!{ELOOP} ? 'is a symbolic link' : $!) . ".\n";
	return undef;
    }
    my @st = stat ($in);
    if (!@st || !S_ISREG ($st[2])) {
	print "Skipping $src: not a regular file.\n";
	close ($in);
	return undef;
    }
    my $dst = "$temp_dir/" . basename ($src);
    if (!copy ($in, $dst)) {
	print "Couldn't stage $src to $dst. $!\n";
	close ($in);
	return undef;
    }
    close ($in);
    print "DEBUG: staged $src as $dst\n" if ($debug_flag);
    return ($dst);
}

# Install a package with pkg_add.
# Should fail if not signed by a key in /etc/signify.
# (But there's a TRUSTED_PKG_PATH bypass...)
# $file is the staged copy in the private temp dir (see stage_file).
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

    # pkg_add does its own signature check (against any key in
    # /etc/signify); because $file is our private staged copy, the
    # package it installs is the same one verify_signature approved
    # under this script's stricter key policy.
    print "DEBUG: installing package $file\n" if ($debug_flag);
    if (system ($PKG_ADD, $file)) {
	return 0; # failure (system returns nonzero for failure)
    }
    else {
	return 1; # success (system returns 0 for success)
    }
}

# Builtin minimal pkg_add, called after signature already verified.
# $file is the staged copy in the private temp dir (see stage_file), so the
# bytes verified are the bytes read here; no second verification is needed.
# The new package's +CONTENTS is fully parsed and validated BEFORE any older
# version is deleted, so a malformed package can't leave neither installed.
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

    $file_minus_tgz = basename ($file);
    $file_minus_tgz =~ s/\.tgz$//;

    # Get content of +CONTENTS file and validate.
    if ($content = $tar->get_content ('+CONTENTS')) {
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

    # Parse +CONTENTS. Everything that can make us die or reject the
    # package happens here, before an older version is deleted. Existence
    # of directories is checked later, at creation time, because deleting
    # the older version may remove directories that exist now.
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
		# Directories: allow sticky and setgid, reject setuid.
		die "Aborting: setuid bit not allowed on directory $line in $file +CONTENTS.\n"
		    if ($current_mode & 04000);
		push (@dirs_to_create, $line);
		$dir_mode{$line} = $current_mode;
	    }
	    elsif (valid_filepath ($line)) { # otherwise it's a file
		# Files: reject all special bits.
		die "Aborting: special mode bits not allowed on file $line in $file +CONTENTS.\n"
		    if ($current_mode & 07000);
		$last_file = $line;
		$file_mode{$line} = $current_mode;
		if ($line =~ /^$OPENBSD_PERL/) {
		    $substitute_line = $line;
		    # The perl lib dir we may create gets 0755, not the module's
		    # file mode (a 0644 directory isn't searchable).
		    if ($^O eq 'linux') {
			$substitute_line =~ s/^$OPENBSD_PERL/$LINUX_PERL/;
			$substitute_linux = 1;
			push (@dirs_to_create, $LINUX_PERL);
			$dir_mode{$LINUX_PERL} = 0755;
		    }
		    elsif ($^O eq 'darwin') {
			$substitute_line =~ s/^$OPENBSD_PERL/$MACOS_PERL/;
			$substitute_macos = 1;
			push (@dirs_to_create, $MACOS_PERL);
			$dir_mode{$MACOS_PERL} = 0755;
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
	# Special bits are checked when the mode is applied to a file or dir
	# line above, where we know which it is.
	elsif ($line =~ /^\@mode\s+(\S+)$/) {
	    my $mode = oct($1);
	    # Reject world-writeable regardless of file type
	    if ($mode & 0002) {
		die "Aborting: world-writeable mode not allowed in \@mode: $1\n";
	    }
	    $current_mode = $mode;
	    print "DEBUG: setting mode to $1 (octal) = $current_mode (decimal)\n" if ($debug_flag);
	}
	elsif ($line =~ /^\@mode\s*$/) {
	    # @mode with no argument resets to default mode
	    $current_mode = 0755;
	    print "DEBUG: resetting mode to default (0755)\n" if ($debug_flag);
	}
	# timestamps
	elsif ($line =~ /^\@ts (\d+)$/) {
	    $file_ts{$last_file} = $1 if (defined ($last_file));
	}
	elsif ($line =~ /^\@sample (.*)$/) {
	    $sample_file = $1;
	    $sample_file = expand_pkg_vars ($sample_file);  # expand ${VARBASE} etc.
	    if (!valid_filepath ($sample_file)) {
		die "Aborting due to unusual \@sample file path in $file +CONTENTS. $line\n";
	    }
	    # Trailing / is a dir to create, most likely in /etc.
	    if ($sample_file =~ /\/$/) {
		die "Aborting: setuid bit not allowed on \@sample directory $sample_file in $file +CONTENTS.\n"
		    if ($current_mode & 04000);
		push (@dirs_to_create, $sample_file);
		$dir_mode{$sample_file} = $current_mode;
	    }
	    # A file to extract into another location if not already present.
	    # Will typically be last file from @files_to_extract. Key is
	    # file in tar file, value is full path of destination.
	    else {
		die "Aborting: \@sample $sample_file precedes any file in $file +CONTENTS.\n"
		    if (!defined ($last_file));
		die "Aborting: special mode bits not allowed on \@sample file $sample_file in $file +CONTENTS.\n"
		    if ($current_mode & 07000);
		$samples_to_extract{$last_file} = $sample_file;
		$file_mode{$sample_file} = $current_mode;
	    }
	}
    }

    if (!-e $PKG_DIR) {
	print "DEBUG: creating $PKG_DIR\n" if ($debug_flag);
	make_path ($PKG_DIR, { error => \my $err });
	if (@$err) {
	    print "Couldn't create $PKG_DIR. $!\n";
	    return 0; # didn't get to installation
	}
    }

    # Set directory, packages extract to /usr/local. Done before deleting
    # any older version so a failure here leaves the old version in place.
    if (!chdir ($DIR_PREFIX)) {
	print "Cannot chdir to $DIR_PREFIX. $! Not installing $file.\n";
	return 0;
    }
    $tar->setcwd ( cwd() );

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

    # Two cases where dirs to create are absolute paths: $MACOS_PERL and @sample dirs.
    # Only directories that don't already exist are created and have their
    # mode set; existing directories are left as they are.
    print "DEBUG: creating any required directories\n" if ($debug_flag);
    print "DEBUG: \@dirs_to_create = @dirs_to_create\n" if ($debug_flag);
    foreach $dir (@dirs_to_create) {
	# Absolute paths (macOS perl modules under /Library/Perl, @sample dirs
	# under /etc) are used as-is; relative paths live under /usr/local.
	my $full_path = ($dir =~ m{^/}) ? $dir : "$DIR_PREFIX/$dir";
	next if (-e $full_path);
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
	    apply_mode($dir_mode{$dir}, $full_path, 1);
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
		apply_mode($file_mode{$file_extracted}, $full_path, 0);
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
			if (defined($file_mode{$substitute_extract{$substitute_file}})) {
			    my $full_path = "$DIR_PREFIX/$substitute_extract{$substitute_file}";
			    apply_mode($file_mode{$substitute_extract{$substitute_file}}, $full_path, 0);
			}
		    }
		    if ($substitute_macos) {
			# already an absolute path for macOS.
			set_timestamp_and_gid ($substitute_extract{$substitute_file}, $file_ts{$substitute_file} // 0);
			# Set mode on substituted file
			if (defined($file_mode{$substitute_extract{$substitute_file}})) {
			    my $full_path = $substitute_extract{$substitute_file};
			    apply_mode($file_mode{$substitute_extract{$substitute_file}}, $full_path, 0);
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
		    apply_mode($file_mode{$samples_to_extract{$tar_source}}, $full_path, 0);
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
	    my $new_pkg_display_hash = get_pkg_display_hash ($file_minus_tgz);
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

# Subroutine to apply a mode to given files.
sub apply_mode {
    my ($mode, $path, $is_dir) = @_;
    
    if ($is_dir) {
        # Directories: allow sticky (01000) and setgid (02000), reject setuid (04000)
        if ($mode & 04000) {
            die "Aborting: setuid bit not allowed on directory $path\n";
        }
    }
    else {
        # Files: reject all special bits
        if ($mode & 07000) {
            die "Aborting: special mode bits not allowed on file $path\n";
        }
    }
    
    if (!chmod($mode, $path)) {
        print "DEBUG: could not set mode " . sprintf("%04o", $mode) . 
              " on " . ($is_dir ? "directory" : "file") . " $path. $!\n" if ($debug_flag);
    }
    else {
        print "DEBUG: set mode " . sprintf("%04o", $mode) . 
              " on " . ($is_dir ? "directory" : "file") . " $path\n" if ($debug_flag);
    }
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

    if (opendir (my $dir_fh, $PKG_DIR)) {
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
        return $ctx->b64digest;
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
	# @sample is already a full path (after expanding ${SYSCONFDIR} etc.,
	# which the registered +CONTENTS still contains, as on install).
	elsif (/^\@sample (.*)$/) {
	    $sample_file = expand_pkg_vars ($1);

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
		
		    $check_sha = $ctx->b64digest;
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

# Extract contents of a signed package. Returns (\@lines, $error): the
# CHANGELOG lines for the entries written and, if extraction stopped part
# way, the error (undef on success). Returns an empty list if the package
# was not verified or could not be read, in which case nothing was written.
# $file is the staged copy in the private temp dir (see stage_file), so the
# file verified is the file extracted.
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
    if (!chdir ('/')) {
	print "Cannot chdir to /. $! Could not extract $file.\n";
	return;
    }
    $tar = Archive::Tar->new;
    if (!$tar->read($file)) {
	print "Couldn't read tar file $file. $!\n";
	return;
    }
    $tar->setcwd ( cwd() );
    print "DEBUG: extracting tar file $file\n" if ($debug_flag);

    # One entry at a time, in archive order, so that if one cannot be
    # written (an immutable file whose syslock group was not unlocked,
    # say) we know which entries before it were. Archive::Tar's own
    # extract() stops at the first failure and returns nothing, which
    # made a partial install look like nothing installed.
    @fileobjs = $tar->get_files;
    foreach $fileobj (@fileobjs) {
	if (!$tar->extract ($fileobj)) {
	    my $eperm = $!{EPERM};   # capture before anything else sets $!
	    my $error = $tar->error || 'unknown error';
	    $error =~ s/\s+\z//;
	    # Archive::Tar replaces a file by unlinking it and creating a new
	    # one, so an immutable directory fails even when the file itself
	    # was unlocked.
	    $error .= " (operation not permitted: the file or its directory may still be immutable;"
		. " check that syslock groups covering both were unlocked)" if ($eperm);
	    return (\@output, $error);
	}
	# Indent each filename line with a tab, three spaces, and a leading slash.
	$filedir = $fileobj->prefix;
	$filename = $fileobj->name;
	$line = "\t" . $THREE_SPACES . '/' . $filedir . '/' . $filename;
	push (@output, $line);
    }

    return (\@output, undef);
}

# Subroutine to expand package variables.
sub expand_pkg_vars {
    my ($path) = @_;
    $path =~ s/\$\{(\w+)\}/$PKG_VARS{$1} \/\/ "\${$1}"/ge;
    return $path;
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

    ($signer, $signdate) = Signify::verify_gzip ($gzip_path,
						 { temp_dir => $temp_dir,
						   require_public_key_file => "$SIGNIFY_KEY_NAME.pub",
						   require_secret_key_path => $SIGNIFY_SEC_KEY });
    @errors = Signify::signify_error;
    
    if (!@errors) {
	print "DEBUG: Verified with expected key: $SIGNIFY_KEY_NAME.sec\n" if ($debug_flag);
	return 1;
    }
    
    elsif ($errors[0] =~ /public key is \"(.*)\" but/) {
	# fileparse returns the file name first. (Before install.pl 1.9 and
	# distribute.pl 1.10 this took the directory, "./", so the second
	# verification below could never succeed.)
	($public_key) = fileparse ($1);
	($signer, $signdate) = Signify::verify_gzip ($gzip_path,
						     { temp_dir => $temp_dir,
						       require_public_key_file => $public_key });
	@errors = Signify::signify_error;
	
	if (@errors) {
	    print "@errors";
	    return 0;
	}
	
	($signer_key_file, $signer_key_dir) = fileparse ($signer);
	# fileparse leaves the trailing slash on the directory. A bare key
	# name (signify since OpenBSD 7.8) gives './'.
	if ($signer_key_dir ne "$SIGNIFY_PUB_KEY_DIR/" && $signer_key_dir ne './') {
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
    # ([a-o])? not ([a-o]?): the latter captures '' (defined) when there is
    # no alpha, which made any vN here die as "both an alpha patch and vN".
    elsif ($version =~ /^(\d{4})\.*(\d{2})(\d{2})([a-o])?(p\d+)?(v\d+)?$/) {
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
