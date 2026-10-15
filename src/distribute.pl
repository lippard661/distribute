#!/usr/bin/perl
# Script to package up configs or binaries for installation across multiple
# servers, sign them with signify, and distribute them to installation
# locations, where they will be installed by install.pl after shutdown into
# single user mode where immutability can be turned off.
#
# Note: installing certificates requires manually unlocking the etcrare
#   group before running install.pl [No longer true, syslock groups fix that.]
#
# Written 30-31 January to 4 February 2022 by Jim Lippard.
# Modified 8 February 2022 by Jim Lippard to require rrsync on the other
#    end, which forces all of the copied files to go into the /var/install
#    directory.
# Modified 14 February 2022 by Jim Lippard so that find_package will use gt
#    instead of > to select the latest version by version string.
# Modified 16 February 2022 by Jim Lippard to add support for certificate
#    distribution.
# Modified 12 May 2022 by Jim Lippard to add support for external IP address
#    changes.
# Modified 27 January 2023 by Jim Lippard to manually correct permissions
#    on pf.conf for external IP address changes, since cp -p doesn't preserve
#    them.
# Modified 14 March 2023 by Jim Lippard to support file versons with flavors,
#    like emacs-20.8p0-no_x11.tgz.
# Modified 18 August 2023 by Jim Lippard to make the manual correction of
#    pf.conf permissions from 27 January 2023 actually work.
# Modified 28 December 2023 by Jim Lippard to add OpenBSD minimum version
#    on signify key (same check as in install.pl).
# Modified 2 January 2024 by Jim Lippard to use File::Copy instead of system command; cp
#    preserves source permissions and copy uses destination umask.
# Modified 4 January 2024 by Jim Lippard to use pledge/unveil. Of limited value.
# Modified 5 January 2024 by Jim Lippard to rework signify signature
#    validation in pledge/unveil environment and be more robust.
# Modified 7 January 2024 by Jim Lippard to support annual keys
#    and new OpenBSD pkg_add "-pkg" requirement in key name.
# Modified 14 March 2024 by Jim Lippard to improve ip-address change process.
# Modified 23 March 2024 by Jim Lippard to add -6 and -4 options.
# Modified 24 April 2024 by Jim Lippard to use OpenBSD::MkTemp.
# Modified 27 July 2024 by Jim Lippard to use Signify module.
# Modified 20 November 2024 by Jim Lippard to add SYSLOCKGROUPS
#    array to configs, to send signed list of syslock groups to destination,
#    for plain and custom files. For packages, we just assume everything
#    goes into /usr/local or /etc ("local" and "etc" syslock group).
# Modified 4 January 2025 by Jim Lippard to add -p (prior year key) to
#    sign with last year's key (e.g., to distribute new key after year
#    changes!).
# Modified 27 January 2025 by Jim Lippard to get key name from host domain
#    name.
# Modified 27-29 January 2025 by Jim Lippard to move from static hash to
#    parsed config file, add -c config option.
# Modified 2 February 2025 by Jim Lippard to add unveil: to config file for
#    custom types, standardize subroutine naming for custom-related
#    subroutines, add %CUSTOM_PLEDGE hash, and remove most special-casing.
#    Added $HOST as another variable that can be used in the config file,
#    source path for ip-address only. $SIGNIFY_PUB_KEY and $SIGNIFY_PUB_KEY_NEXT
#    can already be used for file or dest.
# Modified 4 February 2025 by Jim Lippard to add unveil-exec: to config
#    file for custom types; unveil: now unveils with r only, use unveil-exec:
#    for rx. Make all system calls use argument list to avoid shell.
# Modified 6 February 2025 by Jim Lippard to re-do custom processing and
#    put into subroutines.
# Modified 7 February 2025 by Jim Lippard to add custom-vars: for custom file
#    types, to pass variables and values from config for use by custom
#    file processing. Fix bug in macro expansion. Spaces are now allowed in
#    values of custom-vars and macros.
# Modified 10 February 2025 by Jim Lippard to add more validation on config
#    parsing and make syslock groups optional.
# Modified 11 February 2025 by Jim Lippard to make dest: prohibited for
#    packages.
# Modified 16 February 2025 by Jim Lippard to fix bugs (can't check for
#    file/dir existence before unveiling if unveiling has already begun;
#    had double declaration of a variable passed as parameter to doas).
# Modified 26 April 2025 by Jim Lippard to fix custom pledge for ip-address
#    and to use getaddrinfo/getnameinfo instead of inet_aton/inet_ntoa.
# Modified 12 May 2025 by Jim Lippard to allow overriding of old IP in
#    ip-address if the DNS record is inaccurate, fix bug in DNS lookup.
# Modified 22 June 2025 by Jim Lippard to allow each wan to have a separate
#    DNS record.
# Modified 2 August 2025 by Jim Lippard to do better version checks (> is
#    preferred to gt).
# Modified 8 August 2025 by Jim Lippard to add -h host option and -d debug option.
# Modified 13 August 2025 by Jim Lippard to take another stab at version comparisons,
#    for OpenBSD package version formats.
# Modified 14 September 2025 by Jim Lippard to convert 'all' to hosts list
#    during config parsing and to support 'all except' followed by a hosts
#    list. First step towards supporting distribution to multiple operating
#    systems, in the future might allow defining host groups.
# Modified 22 September 2025 by Jim Lippard to clean up some regexes and fix bug in
#    processing multiple files.
# Modified 24 September 2025 by Jim Lippard to complain if -h leads to no matches.
# Modified 2 October 2025 by Jim Lippard to change $vv variable name to
#    $v_epoch (OpenBSD Makefile term).
# Modified 9 November 2025 by Jim Lippard to unveil /dev/null for Signify.pm.
# Modified 13 November 2025 by Jim Lippard to not allow OpenBSD signing
#    keys if not on OpenBSD.
# Modified 1 January 2026 by Jim Lippard to fix bug in verify_signature
#    when using secondary keys (pubkey dir no longer recorded).
# Modified 3 January 2026 by Jim Lippard to check for existence of current
#    year signing key and warn about next year's signing key 31 days in
#    advance.
# Modified 4 January 2026 by Jim Lippard to remove & from subroutine calls.
# Modified 4 March 2026 by Jim Lippard to remove tmppath pledge.
# Modified 20 April 2026 by Jim Lippard to fix version comparison typo
#    and remove dead code sign_package (now done by Signify).
# Modified 21 April 2026 by Jim Lippard to add -k (key) option and config
#    file options for pkg-dir and default-signing-key. If a non-standard
#    format key is used for plain or custom files, the user will be warned
#    and prompted to continue. Packages can be signed by any <domain>-<year>-pkg
#    key for which the public key is in /etc/signify (this script doesn't
#    sign packages but expects them to be signify-signed, e.g., with OpenBSD's
#    pkg_sign or manually with signify).
# Modified 2 May 2026 by Jim Lippard to use File::Temp on non-OpenBSD,
#    wipe passphrase from memory after use, change all greps to eq block
#    format, other minor improvements.
# Modified 18 May 2026 by Jim Lippard to better remove leading slashes on destination
#    paths when building packages and check return error codes on rsyncs and collect
#    list of failed hosts to report at exit. Stop using bareword filehandle names.
# Modified 20 May 2026 by Jim Lippard to make second check in verify_signature
#    also fail fast.
# Modified 8 June 2026 by Claude at the direction of Jim Lippard to generate
#    syslock grp files if needed by packages.
# Modified 30 June 2026 by Jim Lippard to fix comparison bug in version_gt
#    and OpenBSD version-parse fallbackfound by Claude Opus 4.8 in
#    install.pl. Also fixed other issues found here: new-IP-address range
#    validation, %s->%S timestamp in package name, add_files partial-failure
#    check, passphrase/temp file cleanup via END block, regex metachar
#    quoting.
# Modified 1 August 2026 by Jim Lippard to allow distributing to the same
#    host distributing is from, by building the packages in the
#    /var/install/<hostname> dir and then leaving them there. Modified
#    install.pl to prefer that directory if present.
#    Reject new IP address that's the same as old IP address, skip
#    file updates for ip-address that don't change for a particular
#    host.
# Modified 2 August 2026 by Jim Lippard to add optional custom-vars
#    require-source-dir and skip-files to _custom_ip_address. Update
#    rsync path for Linux or macOS (though this is largely untested
#    for non-OpenBSD).
# Modified 6 August 2026 by Claude Opus 4.8 at the direction of Jim
#    Lippard to genericize _custom_ip_address as _custom_substitute_files,
#    in preparation for adding another instance for changing ip6 prefix
#    delegations in files. Added ipv6-type custom-var (default "tunnel",
#    can use "prefix delegation" or "other").
# Modified 7 August 2026 by Jim Lippard to add ipv6-endpoint custom-var,
#    make ipv6-name optional, change rules on when to use IPv6 (see below
#    or config). Added partly Claude Opus 4.8 rewritten/refactored code
#    for _custom_ipv6_prefix and new custom file type ipv6-prefix.
# Modified 8 August 2026 by Claude Opus 4.8 at the direction of Jim Lippard
#    to modify ipv6-prefix to rewrite larger prefixes within the changing
#    prefix delegation (and attempt to do so for /56-/60 transitions for
#    longer prefixes that aren't orphaned).
# Modified 24 September 2026 by Claude Opus 4.8 at the direction of Jim
#    Lippard to implement only-files custom var.
#    Any file can be in either a skip-files list or an only-files list, not
#    both. For skip-files, the hosts for which a file is listed do not get
#    that file; hosts and files not mentioned are unaffected. For only-files,
#    once a file is referenced it becomes an allow list for that file: it
#    goes to only those hosts with an only-files entry for it, and is skipped
#    on all others. A file not referenced in only-files is unaffected by it.
# Modified 10 October 2026 by Jim Lippard to update version_parse from latest
#    update in install.pl-1.8.
# Modified 10 October 2026 by Claude Opus 5.5 at the direction of Jim Lippard
#    (version 1.9) to fix issues from a security/correctness review:
#    December next-year-key warning never fired (regex tested the year,
#    not the month); ip-address substitution matched inside longer
#    addresses (1.2.3.4 inside 11.2.3.45) and could substitute the literal
#    string "null" if no old address was found and return was hit; old
#    address lookup could return an IPv6 address; reject leading-zero
#    octets; substituted files now keep their source mode instead of
#    getting umask defaults; ipv6-prefix accepted an invalid new prefix
#    length instead of re-prompting, died on in-file addresses outside the
#    old delegation, and rejected valid 1-character hextets;
#    find_package died comparing flavored versions (version_parse can't
#    parse "-no_x11"), now compares versions only and dies if the newest
#    version exists in more than one flavor; package .grp files contained
#    syslock groups accumulated from every earlier file for that host, now
#    each package gets only its own groups; doas.conf generation checks
#    gendoas.pl's exit status and output and writes with -o into the fake
#    dir, so the local host's doas.conf is staged in $INSTALL_DIR/<host>
#    like any other (requires gendoas.pl 1.6, which always respects -o,
#    and checks its version before running it for the local host;
#    earlier versions overwrote the live /etc/doas.conf for their own
#    host); create_package checks chdir, rename, and write;
#    files staged into $INSTALL_DIR/<host> are removed if the run aborts
#    before shipping; signal handlers so END cleanup runs and terminal echo
#    is restored; EOF on interactive prompts dies instead of looping
#    forever; config validation of host names, absolute dest paths, and
#    matching file/dest counts; substitute-file sources without $HOST are
#    now processed instead of silently ignored; -k rejects paths.
# Modified 15 October 2026 by Claude Opus 5.5 at the direction of Jim
#    Lippard (version 1.10): use Signify.pm 1.3's named-argument calls
#    (sign, sign_gzip, and verify_gzip in verify_signature, the same
#    change as install.pl) and require Signify.pm 1.3. Fix two defects in
#    verify_signature that made the fallback to a key other than this
#    year's always fail (fileparse's return values taken in the wrong
#    order; a key path compared without fileparse's trailing slash), so
#    packages signed with an OpenBSD key, last year's key or another
#    <domain>-<year>-pkg key in /etc/signify were refused. pf.conf's
#    group/other read bits are now removed with Perl's chmod, checked,
#    instead of an unchecked exec of /bin/chmod (which also needed an
#    unveil-exec in the config). Drop the duplicate fattr from the
#    ip-address custom pledge; comment why /dev/null is unveiled.
use strict;
use warnings;
use Archive::Tar;
use File::Basename qw(basename dirname fileparse);
use File::Copy qw(copy cp);
use File::Path qw(rmtree);
use File::Spec;
use if $^O ne 'openbsd', 'File::Temp', qw( :mktemp );
use Getopt::Std;
use IO::Uncompress::Gunzip;
use POSIX qw(strftime);
# 1.3 or later: the named-argument calls below are read by older versions
# as positional arguments (a hash reference as the passphrase or temp dir).
use Signify 1.3 qw(signify_error);
use Sys::Hostname;
use if $^O eq "openbsd", "OpenBSD::MkTemp", qw( mkdtemp );
use if $^O eq "openbsd", "OpenBSD::Pledge";
use if $^O eq "openbsd", "OpenBSD::Unveil";

my $VERSION = 'distribute.pl version 1.10 of 15 October 2026.';

my $INSTALL_DIR = '/var/install';
my $PKG_DIR = '/usr/ports/packages/amd64/all';

# plain: The file goes, as is, to individual hosts.
# package: It's a signed package, it goes, as is, to individual hosts.
# custom: There's a module to deal with special processing, the file
#   may be different for each host and the DEST may need to be specified
#   if the file extracts into the root dir or install dir.
my @TYPES = ('plain', 'custom', 'package');

# Suffix for rsync host name (default for v4; add v6 when v6
# is required for Quantum Fiber IP address change).
my $RSYNC_HOST_SUFFIXv4 = '-distribute';
my $RSYNC_HOST_SUFFIXv6 = '-distributev6';

my $MKDIR = '/bin/mkdir';
my $RSYNC = '/usr/local/bin/rsync';
$RSYNC = '/usr/bin/rsync' if ($^O eq 'linux' || $^O eq 'darwin');
my $SIGNIFY = '/usr/bin/signify';
my $STTY = '/bin/stty';
my $UNAME = '/usr/bin/uname';

my ($year) = (localtime (time()))[5];
$year += 1900;
my $prev_year = $year - 1;
my $next_year = $year + 1;

my $HOSTNAME = hostname();
my (@HOSTNAME_ARRAY) = split (/\./, $HOSTNAME);
my $DOMAINNAME = pop (@HOSTNAME_ARRAY);
$DOMAINNAME = pop (@HOSTNAME_ARRAY) . '.' . $DOMAINNAME;
my $SHORT_HOSTNAME = shift (@HOSTNAME_ARRAY);

my $SIGNIFY_PUB_KEY_DIR = '/etc/signify';
my $SIGNIFY_KEY_NAME = "$DOMAINNAME-$year-pkg";
my $SIGNIFY_SEC_KEY = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NAME.sec";
my $SIGNIFY_PUB_KEY = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NAME.pub";
my $PRIOR_SIGNIFY_KEY_NAME = "$DOMAINNAME-$prev_year-pkg";
my $PRIOR_SIGNIFY_SEC_KEY = "$SIGNIFY_PUB_KEY_DIR/$PRIOR_SIGNIFY_KEY_NAME.sec";
my $PRIOR_SIGNIFY_PUB_KEY = "$SIGNIFY_PUB_KEY_DIR/$PRIOR_SIGNIFY_KEY_NAME.pub";
# next for distributing, not for signing (yet).
my $SIGNIFY_KEY_NEXT_NAME = "$DOMAINNAME-$next_year-pkg";
my $SIGNIFY_PUB_KEY_NEXT = "$SIGNIFY_PUB_KEY_DIR/$SIGNIFY_KEY_NEXT_NAME.pub";
my $SIGNIFY_MIN_YEAR = $prev_year;

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

my $CONFIG_FILE = '/etc/distribute.conf';

my %CONFIG; # was constant, now is generated by parse_config
my @HOSTS; # was constant, now generated by parse_config

### For custom files. Add any new required pledges to the hash
### %CUSTOM_PLEDGE for the , they will only be pledged when that
### file is being distributed.

my @custom_pledges;

# for ip-address:
# dns for the old WAN address lookup. (fattr, for preserving file modes,
# is in the base pledge.)
my %CUSTOM_PLEDGE = ('ip-address' => [ 'dns' ] );

### Variables.

my (%opts, $use_v6, $use_prev_year_key, $rsync_host_suffix, $config_file,
    $host_option, @selected_hosts, $debug_flag);

my ($arg, @args, $file, @files, @process_hosts, $package_path,
    %host_package_path, %host_package_files,
    $host, $date, $temp_dir, $temp_file,
    $dest_path, $dest_dir, $dest_file,
    $have_fake_dir,
    $signify_passphrase, @files_to_ship_and_remove, @rsync_file_list,
    @install_packages);

# Signing key variables (set after config parsing and option processing)
my ($signing_sec_key, $signing_pub_key, $signing_key_name);

# Hash of arrays, one per host.
my %syslock_groups;

# Signify errors.
my @errors;

# Files this run created in $INSTALL_DIR/<host>/, removed by cleanup() if
# the run aborts before shipping starts (otherwise an aborted run could
# leave packages in the local host's dir for install.pl to pick up).
my @created_install_files;
my $shipping_started = 0;

# Set while terminal echo is off for the passphrase prompt.
my $echo_off = 0;

# End block to clean up temp files and wipe passphrase from memory if used.
# "local $?" because cleanup() may call system(), which would otherwise
# overwrite the exit status.
END { local $?; cleanup(); }

# Make INT/TERM/HUP run the END block (default action skips it).
$SIG{INT} = $SIG{TERM} = $SIG{HUP} = sub { die "Caught SIG$_[0], aborting.\n" };

### Main program.

# Get options first.
getopts ('46pdVc:h:k:', \%opts) || exit;

# -V version
if ($opts{'V'}) {
    print "$VERSION\n";
    exit 0;
}

# -4 default and doesn't really do anything.
if ($opts{'4'} && $opts{'6'}) {
    die "-4 and -6 are mutually exclusive.\n";
}

if ($opts{'6'}) {
    $use_v6 = 1;
    $rsync_host_suffix = $RSYNC_HOST_SUFFIXv6;
}
else {
    $use_v6 = 0;
    $rsync_host_suffix = $RSYNC_HOST_SUFFIXv4;
}

if ($opts{'p'}) {
    $use_prev_year_key = 1;
}

# -k custom key option
my $custom_key_option = $opts{'k'};

# -k and -p are mutually exclusive
if ($custom_key_option && $use_prev_year_key) {
    die "-k (custom key) and -p (prior year key) are mutually exclusive.\n";
}

$config_file = $opts{'c'} || $CONFIG_FILE;

# get selected hosts, validation comes after config parsing.
if ($opts{'h'}) {
    $host_option = 1;
    $host = $opts{'h'};
    if ($host =~ /,/) {
	@selected_hosts = split (/,\s*/, $host);
    }
    else {
	push (@selected_hosts, $host);
    }
}
else {
    $host_option = 0;
}

$debug_flag = $opts{'d'};

if ($#ARGV == -1) {
    die "Usage: distribute.pl [-4|-6|-p (prior year key)|-V (version)|-c config|-h hosts(CSV)|-k key|-d debug] [files]\n";
}

# Complain about invalid domain name or short hostname (like install.pl).
# Die if weird characters in domain name.
die "Invalid domain name: $DOMAINNAME\n" unless ($DOMAINNAME =~ /^[\w.-]+$/);
# Die if weird characters in short host name.
die "Invalid host name: $SHORT_HOSTNAME\n" unless ($SHORT_HOSTNAME =~ /^[\w.-]+$/);

# Parse config file.
print "DEBUG: parsing config file $config_file\n" if ($debug_flag);
parse_config ($config_file);

# Override PKG_DIR if specified in config
if (defined($CONFIG{_GLOBAL}{PKG_DIR})) {
    $PKG_DIR = $CONFIG{_GLOBAL}{PKG_DIR};
    print "DEBUG: Using PKG_DIR from config: $PKG_DIR\n" if ($debug_flag);
}

# Select signing key for plain/custom files
if ($custom_key_option) {
    die "-k takes a key name in $SIGNIFY_PUB_KEY_DIR, not a path: $custom_key_option\n" if ($custom_key_option =~ m{/});
    $signing_key_name = $custom_key_option;
    $signing_key_name .= '.sec' unless ($signing_key_name =~ /\.sec$/);
    $signing_sec_key = "$SIGNIFY_PUB_KEY_DIR/$signing_key_name";
    $signing_pub_key = $signing_sec_key;
    $signing_pub_key =~ s/\.sec$/.pub/;
    
    die "Custom signing key not found: $signing_sec_key\n" unless (-e $signing_sec_key);
    die "Custom public key not found: $signing_pub_key\n" unless (-e $signing_pub_key);
    
    ($signing_key_name) = basename($signing_sec_key) =~ /^(.*)\.sec$/;
    print "DEBUG: Using custom signing key: $signing_key_name\n" if ($debug_flag);
}
elsif ($use_prev_year_key) {
    # -p option: use prior year key
    $signing_sec_key = $PRIOR_SIGNIFY_SEC_KEY;
    $signing_pub_key = $PRIOR_SIGNIFY_PUB_KEY;
    $signing_key_name = $PRIOR_SIGNIFY_KEY_NAME;
    
    print "DEBUG: Using prior year signing key: $signing_key_name\n" if ($debug_flag);
}
elsif (defined($CONFIG{_GLOBAL}{DEFAULT_SIGNING_KEY})) {
    $signing_key_name = $CONFIG{_GLOBAL}{DEFAULT_SIGNING_KEY};
    $signing_key_name .= '.sec' unless ($signing_key_name =~ /\.sec$/);
    $signing_sec_key = "$SIGNIFY_PUB_KEY_DIR/$signing_key_name";
    $signing_pub_key = $signing_sec_key;
    $signing_pub_key =~ s/\.sec$/.pub/;
    ($signing_key_name) = basename($signing_sec_key) =~ /^(.*)\.sec$/;
    print "DEBUG: Using default signing key from config: $signing_key_name\n" if ($debug_flag);
}
else {
    # Default: use current year key based on domain
    $signing_sec_key = $SIGNIFY_SEC_KEY;
    $signing_pub_key = $SIGNIFY_PUB_KEY;
    $signing_key_name = $SIGNIFY_KEY_NAME;
    
    print "DEBUG: Using default signing key: $signing_key_name\n" if ($debug_flag);
}

# Validate selected signing key exists
if (!-e $signing_sec_key) {
    die "Signing key $signing_sec_key does not exist.\n";
}
if (!-e $signing_pub_key) {
    die "Public key $signing_pub_key does not exist.\n";
}

# Validate readability of signing key.
if (!-r $signing_sec_key) {
    die "Signing key $signing_sec_key is not readable.\n";
}

# Warn if signing key doesn't follow domain-year-pkg pattern
if ($signing_key_name !~ /^\Q$DOMAINNAME\E-\d+-pkg$/) {
    print "\n";
    print "Warning: Signing key '$signing_key_name' doesn't follow the standard pattern.\n";
    print "Expected pattern: $DOMAINNAME-YEAR-pkg (e.g., $DOMAINNAME-2026-pkg)\n";
    print "\n";
    print "Plain/custom files signed with this key will require explicit user\n";
    print "acceptance during installation on target systems.\n";
    print "\n";
    if (!yes_or_no("Continue with non-standard signing key? [y/n]: ")) {
        die "Aborted: non-standard signing key rejected.\n";
    }
    print "\n";
}

# Validate.
foreach $arg (@ARGV) {
    die "Unknown file. $arg\n" if (!defined ($CONFIG{$arg}));
    die "Error in config. Undefined TYPE \"$CONFIG{$arg}{TYPE}\".\n" if (!grep { $_ eq $CONFIG{$arg}{TYPE} } @TYPES);
    push (@files, $arg);
    if ($CONFIG{$arg}{TYPE} eq 'custom') {
	push (@custom_pledges, @{$CUSTOM_PLEDGE{$arg}}) if ($CUSTOM_PLEDGE{$arg});
    }
}

# Validate @selected_hosts;
if ($opts{'h'}) {
    foreach $host (@selected_hosts) {
	die "-h $opts{'h'} specifies host not defined in config. $host\n" if (!grep { $_ eq $host } @HOSTS);
    }
}

# Get the date (YYMMDD-HHMMSS).
$date = strftime ("%Y%m%d-%H%M%S", localtime (time()));
print "DEBUG: getting date: $date\n" if ($debug_flag);

# Warn about missing next year signing key if month is December.
# $date is YYYYMMDD-HHMMSS, so the month is characters 5-6.
if (!-e $SIGNIFY_PUB_KEY_NEXT && $date =~ /^\d{4}12/) {
    print "Warning: Next year's signing key and public key $SIGNIFY_PUB_KEY_NEXT do not exist.\n";
}

# Use pledge and unveil.
# Already got the date so don't need /usr/share/zoneinfo.
if ($^O eq 'openbsd') {
    my ($dir);
    
    # pledge. stdio already included.
    print "DEBUG: \@custom_pledges = @custom_pledges\n" if ($debug_flag);
    pledge ('rpath', 'wpath', 'cpath', 'exec', 'proc', 'fattr', 'unveil', @custom_pledges) || die "Cannot pledge promises. $!\n";

    # unveil, need read-only for all source locations, read-write-create
    # for destination locations, and read-execute for all commands used.
    # For plain files, get the dirname from path. For packages, they all
    # come from PKG_DIR. For custom -- special cased.
    foreach $file (@files) {
	if ($CONFIG{$file}{TYPE} eq 'plain') {
	    $dir = dirname ($CONFIG{$file}{FILE});
	    unveil ($dir, 'r');
	}
	elsif ($CONFIG{$file}{TYPE} eq 'custom') {
	    my $unveil_file;
	    if (defined ($CONFIG{$file}{UNVEIL})) {
		foreach $unveil_file (@{$CONFIG{$file}{UNVEIL}}) {
		    unveil ($unveil_file, 'r');
		}
	    }
	    if (defined ($CONFIG{$file}{UNVEILEXEC})) {
		foreach $unveil_file (@{$CONFIG{$file}{UNVEILEXEC}}) {
		    unveil ($unveil_file, 'rx');
		}
	    }
	}
    }
    unveil ($PKG_DIR, 'r');

    # unveil commands.
    unveil ($MKDIR, 'rx');
    unveil ($RSYNC, 'rx');
    unveil ($SIGNIFY, 'rx');
    unveil ($STTY, 'rx');

    # Signify keys.
    unveil ($SIGNIFY_PUB_KEY_DIR, 'r');

    # For Signify gzip verification: its forked child opens /dev/null for
    # writing with open(2). Since OpenBSD 7.9 only libc's __pledge_open(2)
    # bypasses unveil for /dev/null, so this unveil is required ('c'
    # because '>' opens with O_CREAT).
    unveil ('/dev/null', 'rwc');

    # Installation dir and temp dir.
    unveil ($INSTALL_DIR, 'rwc');
    unveil ('/tmp', 'rwc');

    # Required for Archive::Tar for some reason.
    unveil ('/', 'r');
    
    unveil ();
}

# Process.
# Create temp dir. We didn't used to need it for packages but we do now
# for signify signature verification due to error output going there.
$temp_dir = mkdtemp ('/tmp/distribute.XXXXXXX');
chomp ($temp_dir);

foreach $file (@files) {
    @process_hosts = ();
    print "DEBUG: processing file $file\n" if ($debug_flag);

    print "DEBUG: \@{\$CONFIG{\$file}{HOSTS}} = @{$CONFIG{$file}{HOSTS}}\n" if ($debug_flag);
    print "DEBUG: \@selected_hosts = @selected_hosts\n" if ($debug_flag && $host_option);

    # Put relevant hosts in @process_hosts.
    foreach $host (@{$CONFIG{$file}{HOSTS}}) {
	next if ($host_option && !grep { $_ eq $host } @selected_hosts);
	push (@process_hosts, $host);
    }

    # In-place plain files are no-op for distribution to the local host.
    if ($CONFIG{$file}{TYPE} eq 'plain') {
	my $src = File::Spec->canonpath($CONFIG{$file}{FILE});
	my $dst = File::Spec->canonpath($CONFIG{$file}{DEST} // $CONFIG{$file}{FILE});
	if ($src eq $dst && grep { $_ eq $SHORT_HOSTNAME } @process_hosts) {
	    warn "Skipping local host $SHORT_HOSTNAME for $file: "
		. "file and dest are identical ($src) -- no-op.\n";
	    @process_hosts = grep { $_ ne $SHORT_HOSTNAME } @process_hosts;
	    
	    # If that emptied the list, nothing to build/ship for this file.
	    if (!@process_hosts) {
		warn "No remaining hosts for $file after local no-op removal; skipping.\n";
		next;
	    }
	}
    }

    # Complain/die if -h selected no hosts.
    die "No selected hosts match for file $file. @selected_hosts\n" if ($host_option && @process_hosts == 0);
    
    # Accumulate syslock groups for the per-host plain/custom bundle. Each
    # package gets its own .grp with only its own groups (below), so
    # packages don't contribute here and don't inherit groups from
    # earlier files.
    if ($CONFIG{$file}{TYPE} ne 'package') {
	foreach $host (@process_hosts){
	    print "DEBUG: processing syslock groups for host $host\n" if ($debug_flag);
	    (@{$syslock_groups{$host}}) = add_syslock_groups ($CONFIG{$file}{SYSLOCKGROUPS}, @{$syslock_groups{$host} // []});
	}
    }

    if ($CONFIG{$file}{TYPE} eq 'package') {
	my @pkg_syslock_groups = add_syslock_groups ($CONFIG{$file}{SYSLOCKGROUPS});
	# Look for most up-to-date package in $PKG_DIR.
	$package_path = find_package ($PKG_DIR, $CONFIG{$file}{FILE});
	print "DEBUG: processing package $package_path\n" if ($debug_flag);
	# Verify signature.
	if (!verify_signature ($package_path, 1)) { # 1 = is_package
	    die "Invalid or missing signature. $package_path\n";
	}
	# Copy package to install directories.
	# We put these into host_package_path so they get shipped, but
	# not into host_package_files which get signed.
	@install_packages = copy_package ($package_path, @process_hosts);

	push (@files_to_ship_and_remove, @install_packages);
	# It's not dest_file or dest_dir in this case, it's just the
	# package filename, so we can add it to host_package_path so
	# that it gets shipped.
	($dest_file, $dest_dir) = fileparse ($package_path);
	foreach $host (@process_hosts) {
	    $host_package_path{$host} = "$INSTALL_DIR/$host/$dest_file";

	    # Create syslock group file if any syslock groups specified.
            if (@pkg_syslock_groups) {
                print "DEBUG: creating syslock group file for package $dest_file for $host\n" if ($debug_flag);
                print "DEBUG: \@pkg_syslock_groups = @pkg_syslock_groups\n" if ($debug_flag);
                
                # Get passphrase if not already obtained (may not have
                # plain/custom files that would normally trigger this).
                if (!defined ($signify_passphrase)) {
                    $signify_passphrase = get_signify_passphrase();
                }
                
                my $grp_file = "$host_package_path{$host}.grp";
                push (@created_install_files, grep { !-e $_ } ($grp_file, "$grp_file.sig"));
                create_syslock_group_file ($grp_file, @pkg_syslock_groups);
                # Sign it.
                if (!Signify::sign ($grp_file, { secret_key_path => $signing_sec_key,
						  passphrase => $signify_passphrase })) {
                    @errors = Signify::signify_error();
                    die "Could not sign syslock group file $grp_file with $signing_key_name: @errors\n";
                }
		# Add directly - already in $INSTALL_DIR/$host/, no copy needed
                push (@files_to_ship_and_remove, $grp_file);
                push (@files_to_ship_and_remove, "$grp_file.sig");
	    }
	}
    }
    elsif ($CONFIG{$file}{TYPE} eq 'plain') {
	# Make sure file exists.
	die "File in config can't be found. $CONFIG{$file}{FILE}\n" if (!-e $CONFIG{$file}{FILE});
	print "DEBUG: processing plain file $file\n" if ($debug_flag);

	# If the destination is different from the source (DEST is used),
	# set up fake temp dir. (Need separate fake temp dir for each host
	# just in case some files are generated or otherwise different per
	# host.)
	if ($CONFIG{$file}{DEST}) {
	    $dest_path = $CONFIG{$file}{DEST};
	    ($dest_file, $dest_dir) = fileparse ($dest_path);
	    $dest_path =~ s{^/+}{}; # remove leading slashes
	    foreach $host (@process_hosts) {
		# Make the fake directory (per-host).
		make_fake_dir ($temp_dir, $dest_dir, $host);
		# Copy the file into it. Preserve permissions.
		cp ($CONFIG{$file}{FILE}, "$temp_dir/$host/$dest_path")
		    || die "Failed to copy $CONFIG{$file}{FILE} to $temp_dir/$host/$dest_path: $!\n";
	    }
	    $have_fake_dir = 1;
	}
	else {
	    $dest_path = $CONFIG{$file}{FILE};
	}
	# Add to file to package list.
	print "DEBUG: \@process_hosts = @process_hosts\n" if ($debug_flag);
	foreach $host (@process_hosts) {
	    print "DEBUG: adding $dest_path to package list for host $host\n" if ($debug_flag);
	    push (@{$host_package_files{$host}}, $dest_path);
	}
    }
    elsif ($CONFIG{$file}{TYPE} eq 'custom') {
	# Make sure file exists. (Ignore filenames with commas or $HOST; the
	# substitute-files engine checks each expanded source.)
	# With commas should probably split it out and check for all, but
	# will have to do $HOST substitution and check all relevant
	# instances.
	die "File in config can't be found. $CONFIG{$file}{FILE}\n" if (!-e $CONFIG{$file}{FILE} && $CONFIG{$file}{FILE} !~ /,|\$HOST/);
	print "DEBUG: processing custom file $file\n" if ($debug_flag);

	# Each is separate, for now. There may end up being some different
	# custom types that have common features.
	if ($file eq 'doas.conf') {
	    _custom_doas_dot_conf ($temp_dir, $CONFIG{$file}{CUSTOMVARS}, $CONFIG{$file}{DEST}, @process_hosts);
	    $have_fake_dir = 1;
	}
	# Change old IP address to new IP address in a list of files for
	# distribution to fnord and nkrumah (see config).
	# Dest dirs are pulled from config:
	# /etc, /etc/mail, /home/_rsyncu/.ssh
	# This does not change /etc/faild.conf for hagbard.
	elsif ($file eq 'ip-address') {
	    my $new_rsync_host_suffix = _custom_ip_address ($temp_dir, $CONFIG{$file}{CUSTOMVARS}, $CONFIG{$file}{FILE}, $CONFIG{$file}{DEST}, @process_hosts);
	    $rsync_host_suffix = $new_rsync_host_suffix; # force v4 or v6 as needed
	    $have_fake_dir = 1;
	}
	# Change IPv6 delegated prefix.
	elsif ($file eq 'ipv6-prefix') {
	    my $new_rsync_host_suffix = _custom_ipv6_prefix ($temp_dir, $CONFIG{$file}{CUSTOMVARS}, $CONFIG{$file}{FILE}, $CONFIG{$file}{DEST}, @process_hosts);
	    $rsync_host_suffix = $new_rsync_host_suffix; # force v4 or v6 as needed
	    $have_fake_dir = 1;
	}
	else {
	    die "Error in config. Don't know how to handle custom type for \"$file\".\n";
	}
    }
    else {
	die "Shouldn't happen. Error in config. Undefined TYPE \"$CONFIG{$file}{TYPE}\".\n";
    }
}

# %host_package_files are packages we created that need to be signed.
# Get passphrase for signing plain/custom files if not already obtained.
if (%host_package_files && !defined ($signify_passphrase)) {
    $signify_passphrase = get_signify_passphrase();
}

# If there were any plain or custom files, create and sign the gzips, then copy
# the packages to the install directory.
foreach $host (keys (%host_package_files)) {
    print "DEBUG: creating package for plain and custom for host $host\n" if ($debug_flag);
    $host_package_path{$host} = create_package ($have_fake_dir, $temp_dir, $date, $host, @{$host_package_files{$host}});
    if (!Signify::sign_gzip ($host_package_path{$host}, { secret_key_path => $signing_sec_key,
							  passphrase => $signify_passphrase })) {
	my @errors = Signify::signify_error();
	die "Could not sign package with $signing_key_name: @errors\n";
    }

    push (@files_to_ship_and_remove, copy_package ($host_package_path{$host}, $host));

    # Create syslock group file if any syslock groups are specified.
    if (@{$syslock_groups{$host} // []}) {
	print "DEBUG: creating syslock group file for $host\n" if ($debug_flag);
	print "DEBUG: \@{\$syslock_groups{\$host}} = @{$syslock_groups{$host}}\n" if ($debug_flag);
	create_syslock_group_file ("$host_package_path{$host}.grp", @{$syslock_groups{$host}});
	# Sign it.
	if (!Signify::sign ("$host_package_path{$host}.grp", { secret_key_path => $signing_sec_key,
							       passphrase => $signify_passphrase })) {
	    @errors = Signify::signify_error();
	    die "Could not sign syslock group file $host_package_path{$host}.grp with $signing_key_name: @errors\n";
	}   
	# Add both syslock group file and signature to @files_to_ship_and_remove.
	push (@files_to_ship_and_remove, copy_package ("$host_package_path{$host}.grp", $host));
	push (@files_to_ship_and_remove, copy_package ("$host_package_path{$host}.grp.sig", $host));
    }
}

# For, e.g., custom substitutions where all were no-ops and there's
# nothing changed to ship, say so.
if (!@files_to_ship_and_remove) {
    print "No changed files to distribute.\n";
}

# Now actually distribute the packages to the destinations.
# Instead of doing one at a time we could ship all at once, which
# might be a lot nicer. Would need to find all the matches and add
# them to the command line list, then use the same list to unlink
# them.
my $had_errors = 0;
my @failed_hosts;
# From here on, staged files are either shipped and removed (remote) or
# intentionally left for install.pl (local), so cleanup() leaves them alone.
$shipping_started = 1;
foreach $host (keys (%host_package_path)) {
    @rsync_file_list = ();
    foreach $package_path (@files_to_ship_and_remove) {
	if ($package_path =~ m{^\Q$INSTALL_DIR\E/\Q$host\E/}) {
	    push (@rsync_file_list, $package_path);
	    # With rsync_wrapper.sh	    
	    # system ("$RSYNC --rsync-path=/usr/local/sbin/rsync_wrapper.sh -avr $package_path $host-rsnapshot:/var/install/");
	    # With rrsync: the authorized_keys file forces rrsync -doas /var/install.
	}	    
    }
    if (!@rsync_file_list) {
	warn "No files to distribute to $host.\n";
	next;
    }
    if ($host eq $SHORT_HOSTNAME) {
	# Skip the rsync and removal; the files are already where they're
	# supposed to be.
	print "Distributed to local host $host.\n";
    }
    else {
	print "Distributing to $host.\n";
	my $rc = system ($RSYNC, '-avr', @rsync_file_list, "$host$rsync_host_suffix:.");
	if ($rc == -1) {
	    warn "Failed to execute rsync for $host: $!\n";
	    $had_errors = 1;
	}
	elsif ($rc & 127) {
	    warn sprintf("rsync for %s died with signal %d\n",
			 $host, ($rc & 127));
	    $had_errors = 1;
	}
	elsif (($rc >> 8) != 0) {
	    warn sprintf("rsync for %s exited with status %d\n",
			 $host, ($rc >> 8));
	    $had_errors = 1;
	}
	push (@failed_hosts, $host) if ($rc != 0);
    }


    if ($host ne $SHORT_HOSTNAME) {
	# Now clean it all up and delete them.
	foreach $file (@rsync_file_list) {
	    unlink ($file);
	}
    }
}

# Exit temp subdir, but stay in /tmp.
chdir ('/tmp');

# Delete temp dir.
rmtree ($temp_dir);

# Report failed hosts.
print "Distribution failed for: @failed_hosts\n" if ($had_errors);

# Exit.
exit 1 if ($had_errors);
exit 0;

### Subroutines.

# Cleanup, called from END block.
sub cleanup {
    system ($STTY, 'echo') if ($echo_off);
    if (!$shipping_started) {
	foreach my $f (@created_install_files) {
	    unlink ($f) if (-e $f);
	}
    }
    if (defined ($signify_passphrase)) {
	$signify_passphrase = "x" x length ($signify_passphrase); # overwrite memory
	$signify_passphrase = '';
    }
    # rmtree refuses to remove a tree containing the cwd, which after a die
    # is often a fake dir inside $temp_dir (before 1.9 the temp dir was
    # left behind on any die after create_package or doas.conf processing).
    if (defined $temp_dir && -d $temp_dir) {
	chdir ('/');
	rmtree($temp_dir);
    }
}

# Subroutine to parse config file.
sub parse_config {
    my ($config_file) = @_;

    my ($context);
    my $GLOBAL_CONTEXT = 1;
    my $FILE_CONTEXT = 2;
    
    my ($line_no, @host_list, @syslock_groups_list,
	$field, $value, $current_name,
	@syslock_groups, $group, @hosts, $host, @except_hosts);
    my ($got_file, $got_dest, $got_type, $got_syslock_groups, $got_hosts);
    my (%macros, $macro_name, $have_macros, $more_to_process);

    $current_name = undef;
    $line_no = 0;
    $context = $GLOBAL_CONTEXT;

    open (my $config_fh, '<', $config_file) || die "Cannot open config file $config_file. $!\n";
    while (<$config_fh>) {
	chomp;
	$line_no++;
	if (/^\s*#|^\s*$/) {
	    # ignore
	}
	# Macro definition. Can occur anywhere so long as definition is before use.
	elsif (/^([\w\-]+)\s*=\s*\"([\S ]+)\"$/) {
	    $field = $1;
	    $value = $2;
	    die "Macro \"$field\" defined a second time on line $line_no. $_\n" if (defined ($macros{$field}));
	    $macros{$field} = $value;
	    $have_macros = 1;
	}
	elsif (/^\s*([\w\-]+):\s*(.*)$/) {
	    $field = $1;
	    $value = $2;

	    # any macros to expand?
	    $more_to_process = 1;
	    while ($have_macros && $more_to_process) {
		if ($value =~ /%%([\w\-]+)%%/) {
		    $macro_name = $1;
		    if (defined ($macros{$macro_name})) {
			$value =~ s/%%$macro_name%%/$macros{$macro_name}/g;
		    }
		    else {
			die "Undefined macro %%$macro_name%% on line $line_no. $_\n";
		    }
		}
		else {
		    $more_to_process = 0;
		}
	    }
	    
	    if ($field eq 'host-list') {
		die "A \"host-list:\" field in file context on line $line_no. $_\n" if ($context == $FILE_CONTEXT);
		die "A second \"host-list:\" field on line $line_no. $_\n" if (@host_list);
		@host_list = split (/,\s*/, $value);
		# Host names become path components ($INSTALL_DIR/<host>,
		# $temp_dir/<host>) and the start of the rsync destination, so
		# no slashes, no "..", no leading "-".
		foreach $host (@host_list) {
		    die "Invalid host name \"$host\" in \"host-list:\" on line $line_no. $_\n"
			unless ($host =~ /^[A-Za-z0-9][\w.-]*$/ && $host !~ /\.\./);
		}
		push (@HOSTS, @host_list); # global like %CONFIG
	    }
	    elsif ($field eq 'syslock-groups-list') {
		die "A \"syslock-groups-list:\" field in file context on lin $line_no. $_\n" if ($context == $FILE_CONTEXT);
		die "A second \"syslock-groups-list:\" field on line $line_no. $_\n" if (@syslock_groups_list);
		@syslock_groups_list = split (/,\s*/, $value);
	    }
	    elsif ($field eq 'default-signing-key') {
		die "A \"default-signing-key:\" field in file context on line $line_no. $_\n" if ($context == $FILE_CONTEXT);
		die "A second \"default-signing-key:\" field on line $line_no. $_\n" if (defined($CONFIG{_GLOBAL}{DEFAULT_SIGNING_KEY}));
		
		# Expand variables
		$value =~ s/\$DOMAINNAME/$DOMAINNAME/g;
		$value =~ s/\$YEAR/$year/g;

		# Check for standard format.
		if ($value !~ /^[\w\.\-]+-\d+-pkg$/) {
		    print "Warning: default-signing-key '$value' doesn't follow standard pattern (domain-year-pkg)\n";
		    print "This key will require user prompting during installation.\n";
		}
		
		$CONFIG{_GLOBAL}{DEFAULT_SIGNING_KEY} = $value;
	    }
	    elsif ($field eq 'pkg-dir') {
		die "A \"pkg-dir:\" field in file context on line $line_no. $_\n" if ($context == $FILE_CONTEXT);
		die "A second \"pkg-dir:\" field on line $line_no. $_\n" if (defined($CONFIG{_GLOBAL}{PKG_DIR}));
		
		$CONFIG{_GLOBAL}{PKG_DIR} = $value;
	    }
	    elsif ($field eq 'name') {
		if ($context == $GLOBAL_CONTEXT) {
		    die "No \"host-list:\" defined before first \"name:\" field on line $line_no. $_\n" unless (@host_list);
		    $context = $FILE_CONTEXT;
		}
		if (defined ($current_name)) {
		    # Did we get required fields for previous? Also need to check this at end of file for the last one.
		    die "No \"file:\" defined for \"name: $current_name\" before next \"name:\" on line $line_no. $_\n" if (!$got_file);
		    die "No \"type:\" defined for \"name: $current_name\" before next \"name:\" on line $line_no. $_\n" if (!$got_type);
		    # syslock-groups should always be optional.
#		    die "No \"syslock-groups:\" defined for \"name: $current_name\" before next \"name:\" on line $line_no. $_\n" if (!$got_syslock_groups && $CONFIG{$current_name}{TYPE} ne 'package' && @syslock_groups_list); # optional for packages, or for everything if no syslock-groups-list defined.
		    die "No \"hosts:\" defined for \"name: $current_name\" before next \"name:\" on line $line_no. $_\n" if (!$got_hosts);
		    $got_file = 0;
		    $got_dest = 0;
		    $got_type = 0;
		    $got_syslock_groups = 0;
		    $got_hosts = 0;
		}
		$current_name = $value;
		die "A second \"name:\" using $value on line $line_no. $_\n" if (defined ($CONFIG{$current_name}{FILE}));
		$CONFIG{$current_name}{FILE} = '';
	    }
	    elsif ($field eq 'file') {
		die "A \"file:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		die "A second \"file:\" for $current_name on line $line_no. $_\n" if ($got_file);
		if ($current_name eq "$DOMAINNAME-pkg.pub-current") {
		    $value = $SIGNIFY_PUB_KEY if ($value eq '$SIGNIFY_PUB_KEY');
		}
		elsif ($current_name eq "$DOMAINNAME-pkg.pub-next") {
		    $value = $SIGNIFY_PUB_KEY_NEXT if ($value eq '$SIGNIFY_PUB_KEY_NEXT');
		}
		$CONFIG{$current_name}{FILE} = $value;
		$got_file = 1;
	    }
	    elsif ($field eq 'dest') {
		die "A \"dest:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		die "A second \"dest:\" for $current_name on line $line_no. $_\n" if ($got_dest);
		if ($current_name eq "$DOMAINNAME-pkg.pub-current") {
		    $value = $SIGNIFY_PUB_KEY if ($value eq '$SIGNIFY_PUB_KEY');
		}
		elsif ($current_name eq "$DOMAINNAME-pkg.pub-next") {
		    $value = $SIGNIFY_PUB_KEY_NEXT if ($value eq '$SIGNIFY_PUB_KEY_NEXT');
		}
		# Dest paths are made relative by stripping the leading slash;
		# a relative dest would lose its first character.
		foreach my $dp (split (/,/, $value)) {
		    die "A \"dest:\" path must be absolute, \"$dp\" on line $line_no. $_\n" unless ($dp =~ m{^/});
		}
		$CONFIG{$current_name}{DEST} = $value;
		$got_dest = 1; # optional; forbidden for package type
		if ($got_type && $CONFIG{$current_name}{TYPE} eq 'package') {
		    die "A \"dest:\" field is not permitted for \"package\" type file \"$current_name\" on line $line_no. $_\n";
		}
	    }
	    elsif ($field eq 'type') {
		die "A \"type:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		die "A second \"type:\" for $current_name on line $line_no. $_\n" if ($got_type);
		die "Invalid type \"$value\" on line $line_no. $_\n" if (!grep { $_ eq $value } @TYPES);
		$CONFIG{$current_name}{TYPE} = $value;
		$got_type = 1;
		if ($got_dest && $CONFIG{$current_name}{TYPE} eq 'package') {
		    die "A \"dest:\" field is not permitted for \"package\" type file \"$current_name\" on line $line_no. $_\n";
		}
	    }
	    elsif ($field eq 'syslock-groups') {
		die "A \"syslock-groups:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		die "A \"syslock-groups:\" field used with no \"syslock-groups-list:\" defined on line $line_no. $_\n" unless (@syslock_groups_list);
		die "A second \"syslock-groups:\" for $current_name on line $line_no. $_\n" if ($got_syslock_groups);
		@syslock_groups = split (/,\s*/, $value);
		foreach $group (@syslock_groups) {
		    next if grep { $_ eq $group } @syslock_groups_list;
		    die "Unknown syslock group \"$group\" in \"syslock-groups:\" field on line $line_no. $_\n";
		}
		push (@{$CONFIG{$current_name}{SYSLOCKGROUPS}}, @syslock_groups);
		$got_syslock_groups = 1;
	    }
	    elsif ($field eq 'unveil') {
		die "An \"unveil:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		# for custom only
		die "An \"unveil:\" found for non-custom $current_name on line $line_no. $_\n" if ($CONFIG{$current_name}{TYPE} ne 'custom');
		die "A second \"unveil:\" for $current_name on line $line_no. $_\n" if (defined ($CONFIG{$current_name}{UNVEIL}));
		push (@{$CONFIG{$current_name}{UNVEIL}}, split (/,\s*/, $value));
	    }
	    elsif ($field eq 'unveil-exec') {
		die "An \"unveil-exec:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		# for custom only
		die "An \"unveil-exec:\" found for non-custom $current_name on line $line_no. $_\n" if ($CONFIG{$current_name}{TYPE} ne 'custom');
		die "A second \"unveil-exec:\" for $current_name on line $line_no. $_\n" if (defined ($CONFIG{$current_name}{UNVEILEXEC}));
		push (@{$CONFIG{$current_name}{UNVEILEXEC}}, split (/,\s*/, $value));
	    }
	    elsif ($field eq 'custom-vars') {
		die "A \"custom-vars:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		# for custom only
		die "An \"custom-vars:\" found for non-custom $current_name on line $line_no. $_\n" if ($CONFIG{$current_name}{TYPE} ne 'custom');
		die "A second \"custom-vars:\" for $current_name on line $line_no. $_\n" if (defined ($CONFIG{$current_name}{CUSTOMVARS}));
		my @custom_vars = split (/,\s*/, $value);
		my $custom_var;
		foreach $custom_var (@custom_vars) {
		    if ($custom_var =~ /\s*([\w\-]+)\s*=\s*([\S ]+)$/) {
			${$CONFIG{$current_name}{CUSTOMVARS}}{$1} = $2;
		    }
		    else {
			die "Invalid format in \"custom-vars:\" \"$custom_var\" on line $line_no. $_\n";
		    }
		}
	    }
	    elsif ($field eq 'hosts') {
		die "A \"hosts:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		die "A \"hosts:\" field used with no \"host-list:\" defined on line $line_no. $_\n" unless (@host_list);
		die "A second \"hosts:\" for $current_name on line $line_no. $_\n" if ($got_hosts);
		if ($value eq 'all') {
		    @hosts = @host_list;
		}
		elsif ($value =~ /^all except (.*)$/) {
		    $value = $1;
		    @except_hosts = split (/,\s*/, $value);
		    foreach $host (@except_hosts) {
			next if grep { $_ eq $host } @host_list;
			die "Unknown host \"$host\" in \"hosts:\" field on line $line_no. $_\n";
		    }
		    @hosts = (); # empty array
		    foreach $host (@host_list) {
			next if grep { $_ eq $host } @except_hosts;
			push (@hosts, $host);
		    }
		}
		else { # just a list of hosts
		    @hosts = split (/,\s*/, $value);
		    foreach $host (@hosts) {
			next if grep { $_ eq $host } @host_list;
			die "Unknown host \"$host\" in \"hosts:\" field on line $line_no. $_\n";
		    }
		}
		push (@{$CONFIG{$current_name}{HOSTS}}, @hosts);
		$got_hosts = 1;
	    }
	    else {
		die "Invalid config field name \"$field\" on line $line_no. $_\n";
	    }
	}
	else {
	    die "Unknown config line on line $line_no. $_\n";
	}
    }
    close ($config_fh);

    # Did we get required fields for last "name:"? Same checks as at each subsequent "name:" above.
    die "No \"file:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_file);
    die "No \"type:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_type);
    # syslock-groups should always be optional.
#    die "No \"syslock-groups:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_syslock_groups);
    die "No \"hosts:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_hosts);

    # Multi-file custom entries pair file: and dest: lists one to one;
    # check now rather than after the interactive prompts.
    foreach my $name (keys %CONFIG) {
	next if ($name eq '_GLOBAL' || ($CONFIG{$name}{TYPE} // '') ne 'custom');
	next unless ($CONFIG{$name}{FILE} =~ /,/);
	my @f = split (/,/, $CONFIG{$name}{FILE});
	my $n_file = scalar (@f);
	my @d = split (/,/, $CONFIG{$name}{DEST} // '');
	my $n_dest = scalar (@d);
	die "Config for \"$name\" has $n_file file: entries but $n_dest dest: entries; they must match one to one.\n"
	    if ($n_file != $n_dest);
    }
}

# Subroutine to find a package.
sub find_package {
    my ($pkg_dir, $pkg_start) = @_;
    my (@files, $file, @candidates, $best, @tied);

    if ($pkg_start =~ /^(.*)-PKG$/) {
	$pkg_start = $1;
    }
    else {
	die "Error in config. Package filename doesn't end in \"-PKG\". $pkg_start\n";
    }

    opendir (my $dir_fh, $pkg_dir) || die "Could not open directory $pkg_dir. $!\n";
    @files = grep (!/^\.{1,2}$/, readdir ($dir_fh));
    closedir ($dir_fh);

    # [\w.]+ excludes hyphens, so python-PKG doesn't match
    # python-tkinter-3.x. An optional -no_xxx flavor is captured
    # separately: version_parse can't parse "30.1p0-no_x11", so only the
    # version part is compared.
    foreach $file (sort @files) {
	if ($file =~ /^\Q$pkg_start\E-([\w\.]+)(-no_\w+)?\.tgz$/) {
	    push (@candidates, { file => $file, version => $1, flavor => $2 // '' });
	}
    }
    die "Could not find $pkg_start package in $pkg_dir.\n" if (!@candidates);

    # A single candidate is returned without parsing its version.
    return ("$pkg_dir/$candidates[0]{file}") if (@candidates == 1);

    $best = $candidates[0];
    foreach my $c (@candidates[1..$#candidates]) {
	$best = $c if (version_gt ($c->{version}, $best->{version}));
    }

    # The newest version in more than one flavor (e.g. emacs-30.1p0.tgz and
    # emacs-30.1p0-no_x11.tgz) is ambiguous; don't guess.
    @tied = grep { !version_gt ($best->{version}, $_->{version}) } @candidates;
    if (@tied > 1) {
	die "Ambiguous package for $pkg_start-PKG in $pkg_dir, newest version in more than one flavor: "
	    . join (', ', map { $_->{file} } @tied) . "\n";
    }

    return ("$pkg_dir/$best->{file}");
}

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

# Subroutine to get signify passphrase.
sub get_signify_passphrase {
    my ($signify_passphrase);

    # Set up signal handler to restore echo on interrupt
    local $SIG{INT} = sub { 
        system ($STTY, 'echo'); 
        die "Interrupted\n"; 
    };
    
    # Get signify passphrase.
    system ($STTY, '-echo');
    $echo_off = 1;
    print "signify passphrase: ";
    $signify_passphrase = <STDIN>;
    system ($STTY, 'echo');
    $echo_off = 0;
    die "\nNo passphrase entered (EOF).\n" unless (defined ($signify_passphrase));
    print "\n"; # newline after silent input
    chomp ($signify_passphrase) if (defined ($signify_passphrase));
    return ($signify_passphrase);
}

# Subroutine to copy package to appropriate install dirs.
sub copy_package {
    my ($pkg_path, @hosts) = @_;
    my ($host, $file_basename, @ship_files);

    $file_basename = basename($pkg_path);
    foreach $host (@hosts) {
	my $dst = "$INSTALL_DIR/$host/$file_basename";
	# Track only files this run creates, so an abort doesn't remove a
	# file left by an earlier run that is still waiting for install.pl.
	my $preexisting = -e $dst;
	copy ($pkg_path, $dst)
	    || die "Failed to copy $pkg_path to $INSTALL_DIR/$host: $!\n";
	push (@created_install_files, $dst) unless ($preexisting);
	push (@ship_files, $dst);
    }
    
    return (@ship_files);
}

# Subroutine to create package tar file for a host. This has to be done
# all at once for a gzipped tar file -- the "r" command won't work.
sub create_package {
    my ($have_fake_dir, $temp_dir, $date, $host, @file_list) = @_;
    my ($pkg_path, $file, $file_wo_slash);

    # Relative entries in @file_list live under $temp_dir/$host. A host
    # with only absolute paths may have no fake dir even when another
    # host does; go to / so a failed chdir can't leave us in some other
    # host's fake dir.
    if ($have_fake_dir) {
	if (-d "$temp_dir/$host") {
	    chdir ("$temp_dir/$host") || die "Cannot chdir to $temp_dir/$host. $!\n";
	}
	else {
	    chdir ('/') || die "Cannot chdir to /. $!\n";
	}
    }

    $pkg_path = "$temp_dir/$host-$date-package.tgz";

    if (-e $pkg_path) {
	die "Error, $pkg_path already exists.\n";
    }

    # Using the perl module is better than calling system on the command and piping
    # STDERR to /dev/null to avoid the error message about stripping the initial /.
    # The module won't extract with a leading slash so we need to remove them.
    my $tar = Archive::Tar->new;
    # Relative paths (fake-dir files) are read from the cwd set above.
    # Absolute paths are read from the real filesystem.
    my @added = $tar->add_files (@file_list);
    if (@added != @file_list) {
	die "Failed to add all files to package for $host: got "
	    . scalar(@added) . " of " . scalar(@file_list)
	    . ". " . $tar->error . "\n";
    }
    foreach $file (@file_list) {
	$file_wo_slash = $file;
	$file_wo_slash =~ s/^\///;
	next if ($file_wo_slash eq $file);
	if (!$tar->rename ($file, $file_wo_slash)) {
	    die "Unable to rename $file to $file_wo_slash in tar file. " . $tar->error . "\n";
	}
    }
    # An unchecked partial write (e.g. /tmp full) would get signed and
    # shipped as a truncated archive.
    $tar->write ($pkg_path, COMPRESS_GZIP)
	|| die "Failed to write package $pkg_path for $host. " . $tar->error . "\n";

    return ($pkg_path);
}

# Subroutine to make fake dir for addition of plain files that have
# destinations different from source location. Has to be per-host
# just in case some config files are different per host.
# Returns if the directory already exists.
sub make_fake_dir {
    my ($temp_dir, $dest_dir, $host) = @_;

    return if (-d "$temp_dir/$host$dest_dir");
    system ($MKDIR, '-p', "$temp_dir/$host$dest_dir");
    die "Cannot create $temp_dir/$host$dest_dir.\n" unless (-d "$temp_dir/$host$dest_dir");
}

### Custom packages.

# Subroutine to validate custom variables.
sub _custom_validate_custom_vars {
    my ($file, $custom_vars, %req_opt_custom_vars) = @_;
    my (%custom_vars, $custom_var);

    # No custom-vars: line at all leaves this undef.
    %custom_vars = %{$custom_vars // {}};

    foreach $custom_var (keys (%req_opt_custom_vars)) {
	die "Config is missing required custom variable \"$custom_var\" for $file.\n" if (!defined ($custom_vars{$custom_var}) && $req_opt_custom_vars{$custom_var} eq 'required');
    }

    # Make sure all variables are either required or optional.
    foreach $custom_var (keys (%custom_vars)) {
	die "Config specifies undefined custom variable \"$custom_var\" for $file.\n" if (!grep { $_ eq $custom_var } keys (%req_opt_custom_vars));
    }
}

# Subroutine for custom doas.conf generation and distribution.
sub _custom_doas_dot_conf {
    my ($temp_dir, $custom_vars, $dest_path, @hosts) = @_;
    my (%custom_vars, $dest_file, $dest_dir, $host);
    # global: $have_fake_dir, %host_package_files

    my %REQ_OPT_CUSTOM_VARS = ('gendoas' => 'required');

    _custom_validate_custom_vars ('doas.conf', $custom_vars, %REQ_OPT_CUSTOM_VARS);

    %custom_vars = %{$custom_vars};

    # required custom vars: gendoas=/path/to/gendoas

    my $PERL = '/usr/bin/perl';
    my $GENDOAS = $custom_vars{'gendoas'};

    die "Cannot find $GENDOAS.\n" if (!-e $GENDOAS);

    die "doas.conf dest must be an absolute path: $dest_path\n" unless (defined ($dest_path) && $dest_path =~ m{^/});
    ($dest_file, $dest_dir) = fileparse ($dest_path);
    $dest_path =~ s{^/+}{};
#    $have_fake_dir = 1; # done after call to this subroutine
    # The local host requires gendoas.pl 1.6 or later: earlier versions
    # ignore -o for their own host name and overwrite the live
    # /etc/doas.conf. Check the version before running it for this host.
    if (grep { $_ eq $SHORT_HOSTNAME } @hosts) {
	my $gendoas_version = '';
	if (open (my $v_fh, '-|', $PERL, $GENDOAS, '-V')) {
	    $gendoas_version = <$v_fh> // '';
	    close ($v_fh);
	}
	if ($gendoas_version !~ /version (\d+)\.(\d+)/ || $1 < 1 || ($1 == 1 && $2 < 6)) {
	    chomp ($gendoas_version);
	    die "$GENDOAS is too old to generate doas.conf for local host $SHORT_HOSTNAME (need 1.6+, it would overwrite /etc/doas.conf): '$gendoas_version'\n";
	}
    }

    foreach $host (@hosts) {
	make_fake_dir ($temp_dir, $dest_dir, $host);
	my $out = "$temp_dir/$host/$dest_path";
	chdir ("$temp_dir/$host$dest_dir") || die "Cannot chdir to $temp_dir/$host$dest_dir. $!\n";
	system ($PERL, $GENDOAS, '-o', $out, $host);
	if ($? == -1) {
	    die "Could not run $PERL $GENDOAS: $!\n";
	}
	elsif ($? != 0) {
	    die "$GENDOAS failed for $host (" . (($? & 127) ? 'signal ' . ($? & 127) : 'exit ' . ($? >> 8)) . "); not distributing doas.conf.\n";
	}
	die "$GENDOAS produced no output for $host at $out.\n" unless (-s $out);
	push (@{$host_package_files{$host}}, $dest_path);
    }
}

# Generic engine for custom string-substitution across a set of files:
# stages each source into the fake dir, applies a per-file substitution
# callback, honors skip-files, only-files, and require-source-dir, detects no-ops, and
# packages the result. The substitution itself (what "old" and "new" mean,
# and how they're matched) is entirely in $substitute_cb, so new custom
# types (e.g. ipv6-prefix) reuse this by passing a different callback.
#
# $substitute_cb->($staged_file_path) must perform the substitution in place
# and return the number of changes (0 = no-op for that file/host).
# $label is used only in the no-op warning ('IP' -> "No IP substitutions...").
sub _custom_substitute_files {
    my ($temp_dir, $custom_vars, $file, $dest, $substitute_cb, $label, @hosts) = @_;
    my (%custom_vars, @source_paths, @dest_paths,
        $host, $idx, $source_path, $dest_path,
	%skip_file_hash, %only_file_hash, %only_governed);
    # global: $have_fake_dir, %host_package_files, $dest_file, $dest_dir

    %custom_vars = %{$custom_vars};

    # If require-source-dir is specified and not present, abort immediately.
    if (defined ($custom_vars{'require-source-dir'}) &&
        !-d $custom_vars{'require-source-dir'}) {
        die "Required source dir $custom_vars{'require-source-dir'} is not present.\n";
    }

    # Do this early so that skip-files can use @dest_paths for validation.
    @source_paths = split (/,/, $file);
    @dest_paths = split (/,/, $dest // '');
    die "Config for $label substitution has " . scalar (@source_paths) . " file: entries but "
	. scalar (@dest_paths) . " dest: entries; they must match one to one.\n"
	if (@source_paths != @dest_paths);
    foreach my $dp (@dest_paths) {
	die "Config dest path for $label substitution must be absolute: $dp\n" unless ($dp =~ m{^/});
    }

    # If skip-files is defined, turn it into a hash of hashes.
    if (defined ($custom_vars{'skip-files'})) {
        my @skip_file_values = split (/\&/, $custom_vars{'skip-files'});

        my @dest_file_basenames;
        foreach my $dp (@dest_paths) {
            push (@dest_file_basenames, basename ($dp));
        }

        foreach my $skip_file_value (@skip_file_values) {
            (my $skip_host, my $skip_file) = split (/:/, $skip_file_value, 2);
            die "Malformed skip-files entry (need host:destfile): $skip_file_value\n"
                unless (defined $skip_host && length $skip_host
                        && defined $skip_file && length $skip_file);
            die "Undefined host $skip_host in skip-files custom-var value $skip_file_value.\n" if (!grep { $_ eq $skip_host } @hosts);
            die "Undefined dest file basename $skip_file in skip-files entry: $skip_file_value\n"
                unless (grep { $_ eq $skip_file } @dest_file_basenames);
            $skip_file_hash{$skip_host}{$skip_file} = 1;
        }
    }

    # If only-files is defined, turn it into a hash of hashes and record
    # which dest basenames it governs. only-files is a per-file allow list:
    # once a file is named here it goes ONLY to the listed hosts and is
    # skipped on all others. A file never named here is unaffected by it.
    # A file may appear in skip-files OR only-files, never both.
    if (defined ($custom_vars{'only-files'})) {
        my @only_file_values = split (/\&/, $custom_vars{'only-files'});

        my @dest_file_basenames;
        foreach my $dp (@dest_paths) {
            push (@dest_file_basenames, basename ($dp));
        }

        foreach my $only_file_value (@only_file_values) {
            (my $only_host, my $only_file) = split (/:/, $only_file_value, 2);
            die "Malformed only-files entry (need host:destfile): $only_file_value\n"
                unless (defined $only_host && length $only_host
                        && defined $only_file && length $only_file);
            die "Undefined host $only_host in only-files custom-var value $only_file_value.\n"
                if (!grep { $_ eq $only_host } @hosts);
            die "Undefined dest file basename $only_file in only-files entry: $only_file_value\n"
                unless (grep { $_ eq $only_file } @dest_file_basenames);
            $only_file_hash{$only_host}{$only_file} = 1;
            $only_governed{$only_file} = 1;
        }

        # A file governed by only-files must not also appear in skip-files.
        foreach my $f (keys %only_governed) {
            die "File $f appears in both skip-files and only-files; a file must use one or the other.\n"
                if (grep { exists $skip_file_hash{$_}{$f} } keys %skip_file_hash);
        }
    }

    foreach $host (@hosts) {
        for ($idx = 0; $idx <= $#source_paths; $idx++) {
            $source_path = $source_paths[$idx];
            $dest_path = $dest_paths[$idx];
            ($dest_file, $dest_dir) = fileparse ($dest_path);
            # skip if defined in $skip_file_hash
            next if (defined ($skip_file_hash{$host}{$dest_file}));
            # only-files: if this file is governed and this host isn't listed, skip
            next if ($only_governed{$dest_file}
                     && !$only_file_hash{$host}{$dest_file});
            $dest_path =~ s{^/+}{};
            # $HOST is special-cased (substituted at execution time).
            # A source without $HOST is the same file for every host.
            # (Before 1.9 such a source was silently never processed.)
            $source_path =~ s/\$HOST/$host/;
            if (!-e $source_path) {
                die "Source path missing, can use /var/db/servers if urgent: $source_path\n";
            }

            make_fake_dir ($temp_dir, $dest_dir, $host);
            cp ($source_path, "$temp_dir/$host/$dest_path")
                || die "Failed to copy $source_path to $temp_dir/$host/$dest_path: $!\n";

            my $changed = $substitute_cb->("$temp_dir/$host/$dest_path");

            if (!$changed) {
                warn "No $label substitutions in $dest_path for $host; skipping (no-op for this host).\n";
                unlink ("$temp_dir/$host/$dest_path");
                next; # skip this host for this file
            }

            # The substitution subroutines now preserve the source mode;
            # this stays as a backstop so pf.conf is never group/other
            # readable even if the source copy was.
            if ($dest_path =~ /\/pf\.conf$/) {
                my $pf_path = "$temp_dir/$host/$dest_path";
                my @pf_st = stat ($pf_path);
                if (!@pf_st || !chmod (($pf_st[2] & 07777) & ~0044, $pf_path)) {
                    die "Cannot remove group/other read permission from $pf_path. $!\n";
                }
            }

            push (@{$host_package_files{$host}}, $dest_path);
        }
    }
}

# Subroutine for custom IP address change. Type-specific glue over the
# generic _custom_substitute_files engine: validates ip-address's custom
# vars, acquires old/new addresses (and the v4/v6 rsync suffix), and hands
# the engine a callback that does the dotted + dot-escaped substitution.
sub _custom_ip_address {
    my ($temp_dir, $custom_vars, $file, $dest, @hosts) = @_;
    my (%custom_vars, $old_address, $new_address, $new_rsync_host_suffix);

    my %REQ_OPT_CUSTOM_VARS = ('wan0' => 'required', # name of provider
                               'wan1' => 'optional', # name of provider
                               'wan0-host-fqdn' => 'optional', # FQDN of WAN
                               'wan1-host-fqdn' => 'optional', # FQDN of WAN
                               'require-source-dir' => 'optional', # config file source location
                               'skip-files' => 'optional', # host:file&host:file
			       'only-files' => 'optional', # host:file&host:file
                               'ipv6-name' => 'optional', # name of IPv6 provider
			       'ipv6-type' => 'optional', # tunnel, prefix delegation, or other
			       'ipv6-endpoint' => 'optional', # wan0 or wan1
                               'dns' => 'required'); # name of DNS provider

    _custom_validate_custom_vars ('ip-address', $custom_vars, %REQ_OPT_CUSTOM_VARS);

    %custom_vars = %{$custom_vars};

    # Determine old/new addresses and the v4/v6 suffix to force on rsync.
    # Currently assumes IPv6 is dependent on wan0 IP address as a tunnel endpoint,
    # should implement additional custom-var(s) to specify any dependency or prompt.
    ($old_address, $new_address, $new_rsync_host_suffix) =
        _custom_get_old_and_new_ip_addresses ($custom_vars{'wan0-host-fqdn'}, $custom_vars{'wan1-host-fqdn'}, $custom_vars{'ipv6-name'}, $custom_vars{'ipv6-type'}, $custom_vars{'ipv6-endpoint'}, $custom_vars{'dns'}, $custom_vars{'wan0'}, $custom_vars{'wan1'});

    # 1 = also replace dot-escaped IPs; that flag is ip-address-specific and
    # lives here in the callback, not in the generic engine.
    _custom_substitute_files (
        $temp_dir, $custom_vars, $file, $dest,
        sub { _custom_global_replace_in_file ($_[0], $old_address, $new_address, 1) },
        'IP',
        @hosts);

    return $new_rsync_host_suffix;
}

# Subroutine to get old external IP address from DNS and new
# external IP address via prompt.
# Assumes IPv6 is tunnel over wan0.
# Returns $new_rsync_host_suffix up for $rsync_host_suffix to be changed in main.
sub _custom_get_old_and_new_ip_addresses {
    my ($wan0_host_fqdn, $wan1_host_fqdn, $ipv6_name, $ipv6_type, $ipv6_endpoint, $dns, $wan0, $wan1) = @_;
    use Socket qw( :addrinfo SOCK_RAW AF_INET );
    my ($have_ipv6, $old_address, $new_address, $wan0_or_wan1,
	$lc_wan0, $lc_wan1, $host_fqdn);
    my $new_rsync_host_suffix;

    $lc_wan0 = lc ($wan0);

    if (!defined ($wan1)) {
	$wan0_or_wan1 = $wan0;
    }
    else {
	$wan0_or_wan1 = 'null';
	$lc_wan1 = lc ($wan1);
    }

    if (defined ($ipv6_name)) {
	$have_ipv6 = 1;
	if (!defined ($ipv6_type)) {
	    $ipv6_type = 'tunnel';
	}
	elsif ($ipv6_type ne 'tunnel' && $ipv6_type ne 'prefix delegation' &&
	       $ipv6_type ne 'other') {
	    die "Invalid value for custom-var ipv6-type, must be \"tunnel\", \"prefix delegation\", or \"other\", not \"$ipv6_type\".\n";
	}
	if (!defined ($ipv6_endpoint)) {
	    $ipv6_endpoint = 'wan0';
	}
	elsif ($ipv6_endpoint ne 'wan0' && $ipv6_endpoint ne 'wan1') {
	    die "Invalid value for custom-var ipv6-endpoint, must be \"wan0\" or \"wan1\", not \"$ipv6_endpoint\".\n";
	}
    }
    else {
	$have_ipv6 = 0;
    }

    while ($wan0_or_wan1 eq 'null') {
	print "$wan0 or $wan1? ";
	$wan0_or_wan1 = lc (read_line_or_die());
	$wan0_or_wan1 = 'null' unless ($wan0_or_wan1 eq $lc_wan0 || $wan0_or_wan1 eq $lc_wan1);
    }

    # Use IPv6 if available and not changing an IPv6 tunnel endpoint IP.
    if ($wan0_or_wan1 eq $lc_wan0) {
	if ($have_ipv6 && $ipv6_type eq 'tunnel' && $ipv6_endpoint eq 'wan0') {
	    print "Distributing via v4 since $ipv6_name v6 $ipv6_type is down.\n";
	    print "Warning: Must manually update $ipv6_name $ipv6_type.\n";
	    print "Warning: Must manually update firewall $ipv6_type-related configurations.\n";
	    $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv4;
	    $host_fqdn = $wan0_host_fqdn;
	}
	elsif ($have_ipv6) {
	    print "Distributing via $ipv6_name v6 since it should not be impacted by $wan0 IP change.\n";
	    $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv6;
	    $host_fqdn = $wan0_host_fqdn;
	}
	else {
	    $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv4;
	    $host_fqdn = $wan0_host_fqdn;
	}
	print "Warning: Must manually update DNS record via $dns.\n";
    }
    else { # wan1
	if ($have_ipv6 && $ipv6_type eq 'tunnel' && $ipv6_endpoint eq 'wan1') {
	    print "Distributing via v4 since $ipv6_name v6 $ipv6_type is down.\n";
	    print "Warning: Must manually update $ipv6_name $ipv6_type.\n";
	    print "Warning: Must manually update firewall $ipv6_type-related configurations.\n";
	    $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv4;
	    $host_fqdn = $wan1_host_fqdn;
	}
	elsif ($have_ipv6) {
	    print "Distributing via $ipv6_name v6 since it should not be impacted by $wan1 IP change.\n";
	    $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv6;
	    $host_fqdn = $wan1_host_fqdn;
	}
	else {
	    $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv4;
	    $host_fqdn = $wan1_host_fqdn;
	}
	print "Warning: Must manually update DNS record via $dns.\n";
    }
    if (defined ($host_fqdn)) {
	$old_address = _get_wan_ip ($host_fqdn);
    }
    else {
	$old_address = 'null';
    }
    while (1) {
	print "Old address: $old_address (return or enter correct): ";
	my $input_string = read_line_or_die();
	if (_valid_ipv4 ($input_string)) {
	    $old_address = $input_string;
	    last;
	}
	# Return accepts the looked-up address only if it is a real address;
	# otherwise the literal "null" would be substituted in every file.
	elsif ($input_string eq '' && _valid_ipv4 ($old_address)) {
	    last;
	}
	elsif ($input_string eq '') {
	    print "No old address was found; enter it.\n";
	}
	else {
	    print "Invalid response \"$input_string\". Enter old IP or hit return.\n";
	}
    }

    $new_address = 'null';
    while ($new_address eq 'null') {
	print "New IP Address: ";
	$new_address = read_line_or_die();
	$new_address = 'null' unless (_valid_ipv4 ($new_address));
	if ($new_address eq $old_address) {
	    print "New address $new_address is the same as old address $old_address. Try again.\n";
	    $new_address = 'null';
	}
    }
    
    return ($old_address, $new_address, $new_rsync_host_suffix);
}

# Subroutine to get WAN IP from fqdn.
sub _get_wan_ip {
    my ($host_fqdn) = @_;
    my ($old_address, $err, @res, $ai);

    # AF_INET: without it a WAN name with an AAAA record could return an
    # IPv6 address here, offered as the default old address. Use the first
    # result (the old loop kept the last).
    ($err, @res) = getaddrinfo ($host_fqdn, "", {family => AF_INET, socktype => SOCK_RAW});
    if ($err || !@res) {
	print "Cannot getaddrinfo for $host_fqdn - " . ($err || 'no IPv4 address') . "\n";
	return ('null');
    }
    $ai = $res[0];
    ($err, $old_address) = getnameinfo($ai->{addr}, NI_NUMERICHOST, NIx_NOSERV);
    if ($err) {
	print "Cannot getnameinfo for $host_fqdn - $err\n";
	return ('null');
    }
    return ($old_address);
}

# Strict dotted-quad IPv4: four octets 0-255, no leading zeros (010 could
# be read as octal by some parsers).
sub _valid_ipv4 {
    my ($address) = @_;
    my $octet = qr/(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)/;
    return (defined ($address) && $address =~ /^$octet\.$octet\.$octet\.$octet$/);
}

# Read one line from STDIN, chomped. Dies on EOF instead of letting the
# prompt loops spin forever on undef.
sub read_line_or_die {
    my $line = <STDIN>;
    die "\nEnd of input at prompt, aborting.\n" unless (defined ($line));
    chomp ($line);
    return ($line);
}

# Subroutine to do global string replacement on a given file.
sub _custom_global_replace_in_file {
    my ($file, $string, $replace, $dot_escape) = @_;
    my $backup_file;
    my ($dot_escaped_string, $dot_escaped_replace);

    if (defined ($dot_escape) && $dot_escape) {
	$dot_escaped_string = $string;
	$dot_escaped_string =~ s/\./\\./g;
	$dot_escaped_replace = $replace;
	$dot_escaped_replace =~ s/\./\\./g;
    }
    else {
	$dot_escape = 0;
    }

    $backup_file = $file . '.bak';

    rename ($file, $backup_file) || die "Cannot rename $file to $backup_file. $!\n";
    open (my $infile_fh, '<', $backup_file) || die "Cannot open file. $backup_file $!\n";
    open (my $outfile_fh, '>', $file) || die "Cannot open file for writing. $file $!\n";
    # Keep the source file's mode; the new file would otherwise get umask
    # defaults (e.g. 0644 for a 0600 or 0640 file).
    my $mode = (stat ($infile_fh))[2] & 07777;
    chmod ($mode, $outfile_fh) || die "Cannot set mode on $file. $!\n";
    my $changed = 0;
    # Bounded so 1.2.3.4 doesn't match inside 11.2.3.45 or 1.2.3.45: not
    # preceded by a digit or dot, not followed by a digit or .digit (for
    # the dot-escaped form, not followed by a digit or \.digit).
    while (<$infile_fh>) {
	$changed += s/(?<![\d.])\Q$string\E(?!\.?\d)/$replace/g;
	$changed += s/(?<![\d.])\Q$dot_escaped_string\E(?!\d|\\\.\d)/$dot_escaped_replace/g if ($dot_escape);
	print $outfile_fh $_;
    }
    close ($infile_fh);
    close ($outfile_fh) || die "Error writing $file. $!\n";
    unlink ($backup_file);
    return ($changed); # did anything change?
}

# Subroutine for custom IPv6 prefix delegation change.  Type-specific
# glue over the generic _custom_substitute_files engine: validates
# custom vars, acquires old/new addresses, and provides a callback
# that does the substitution. Assumes at least one prefix delegation
# interface but supports a second.
sub _custom_ipv6_prefix {
    my ($temp_dir, $custom_vars, $file, $dest, @hosts) = @_;
    my %custom_vars;

    my %REQ_OPT_CUSTOM_VARS = ('wan0' => 'required', # name of provider
                               'wan1' => 'optional', # name of provider
			       'wan0-prefix-file' => 'optional', # dhcpleased /var/run/db/dhcp6leased/<interface>, backup has old one
                               'wan1-prefix-file' => 'optional',
                               'require-source-dir' => 'optional', # source of config files
                               'skip-files' => 'optional',  # host:file&host:file
			       'only-files' => 'optional'); # host:file&host:file

    _custom_validate_custom_vars ('ipv6-prefix', $custom_vars, %REQ_OPT_CUSTOM_VARS);

    %custom_vars = %{$custom_vars};

    # Determine old/new prefixes and whether we use IPv4 (if primary IPv6 is down) or IPv6 (if primary IPv6 is up).
    # We assume wan0 is primary IPv6 and wan1 is a backup IPv6.
    my ($old_h123, $old_h4top, $old_len,
        $new_h123, $new_h4top, $new_len, $new_rsync_host_suffix) =
        _custom_get_old_and_new_ip6_prefixes ($custom_vars{'wan0'}, $custom_vars{'wan1'},
                                              $custom_vars{'wan0-prefix-file'}, $custom_vars{'wan1-prefix-file'});

    if ($old_len == $new_len) {
	# same-length: proven-correct numeric substitution, no gating
    }
    elsif ($old_len == 56 && $new_len == 60) {
	# narrowing: auto-proceed, but the substitute pass must die if any
	# matched address's newly-constrained nibble wasn't already the new
	# prefix's value (i.e. would be silently renumbered/orphaned)
    }
    else {  # 60 -> 56, widening
	die "IPv6 prefix widening ($old_len -> $new_len) requires a subnet "
	    . "renumbering decision; handle these files manually.\n";
    }

    _custom_substitute_files (
        $temp_dir, $custom_vars, $file, $dest,
        sub { _custom_ipv6_substitute_in_file ($_[0],
                  $old_h123, $old_h4top, $old_len,
                  $new_h123, $new_h4top, $new_len) },
        'IPv6 prefix delegation',
        @hosts);

    return $new_rsync_host_suffix;
}

# Subroutine to get old and new IPv6 prefix delegation strings.
sub _custom_get_old_and_new_ip6_prefixes {
    my ($wan0, $wan1, $wan0_prefix_file, $wan1_prefix_file) = @_;
    my ($lc_wan0, $lc_wan1, $wan0_or_wan1,
	$old_prefix, $new_prefix);

    $lc_wan0 = lc ($wan0);

    if (!defined ($wan1)) {
	$wan0_or_wan1 = $wan0;
    }
    else {
	$wan0_or_wan1 = 'null';
	$lc_wan1 = lc ($wan1);
    }

    while ($wan0_or_wan1 eq 'null') {
	print "$wan0 or $wan1? ";
	$wan0_or_wan1 = lc (read_line_or_die());
	$wan0_or_wan1 = 'null' unless ($wan0_or_wan1 eq $lc_wan0 || $wan0_or_wan1 eq $lc_wan1);
    }

    $old_prefix = 'null';
    
    # use prefix files if supplied
    if ($wan0_or_wan1 eq $lc_wan0) {
	if (defined ($wan0_prefix_file)) {
	    $old_prefix = _custom_get_prefix_delegation ($wan0_prefix_file);
	}
    }
    else {
	if (defined ($wan1_prefix_file)) {
	    $old_prefix = _custom_get_prefix_delegation ($wan1_prefix_file);
	}
    }

    my $old_prefix_body;
    my $old_prefix_len;
    while (1) {
	print "Old prefix: $old_prefix (return or enter correct): ";
	my $input_string = read_line_or_die();
	$input_string = $old_prefix if ($input_string eq '');
	if ($input_string =~ /^((?:[0-9a-fA-F]{1,4}:){3}[0-9a-fA-F]{1,4})::\/(\d{2})$/) {
	    $old_prefix_body = lc ($1);
	    $old_prefix_len = $2;
	    last if ($old_prefix_len == 56 || $old_prefix_len == 60);
	    warn "Invalid prefix length $old_prefix_len, must be 56 or 60.\n";
	}
	else {
	    print "Invalid response \"$input_string\". Enter new IPv6 prefix or hit return.\n";
	}
    }

    $new_prefix = 'null';
    my $new_prefix_body;
    my $new_prefix_len;
    while ($new_prefix eq 'null') {
	  print "New prefix: ";
	  $new_prefix = read_line_or_die();
	  if ($new_prefix =~ /^((?:[0-9a-fA-F]{1,4}:){3}[0-9a-fA-F]{1,4})::\/(\d{2})$/) {
	      $new_prefix_body = lc ($1);
	      $new_prefix_len = $2;
	      # Compare normalized hextets so 2001:DB8:: equals 2001:db8:: and
	      # 2001:0db8:: equals 2001:db8::.
	      if (_ipv6_norm ($new_prefix_body) eq _ipv6_norm ($old_prefix_body) && $new_prefix_len == $old_prefix_len) {
		  print "New IPv6 prefix $new_prefix is the same as old prefix $old_prefix. Try again.\n";
		  $new_prefix = 'null';
	      }
	      elsif ($new_prefix_len != 56 && $new_prefix_len != 60) {
		  # Re-prompt (before 1.9 the loop exited with the bad length).
		  warn "Invalid prefix length $new_prefix_len, must be 56 or 60. $new_prefix\n";
		  $new_prefix = 'null';
	      }
	  }
	  else {
	      $new_prefix = 'null';
	      next;
	  }
    }

    # At this point $old_prefix and $new_prefix are canonical (hextets 1-3
    # plus hextet 4, no trailing ::/len -- _custom_canonicalize_prefix
    # stripped that). Decompose each into hextets 1-3 and the numeric
    # hextet-4 prefix value for the numeric substitution engine.
    my ($old_h123, $old_h4top) = _ipv6_decompose_prefix ($old_prefix_body, $old_prefix_len);
    my ($new_h123, $new_h4top) = _ipv6_decompose_prefix ($new_prefix_body, $new_prefix_len);

    my $new_rsync_host_suffix = $RSYNC_HOST_SUFFIXv4; # unless wan-dependency vars added later
    return ($old_h123, $old_h4top, $old_prefix_len,
            $new_h123, $new_h4top, $new_prefix_len,
            $new_rsync_host_suffix);
}

# Split a canonical /56 or /60 prefix ("h1:h2:h3:h4") into its first three
# hextets (as a string) and hextet 4 masked to prefix bits only (as a number).
# Assumes _custom_canonicalize_prefix has already validated and canonicalized.
sub _ipv6_decompose_prefix {
    my ($prefix, $len) = @_;

    my @hextets = split (/:/, $prefix);
    die "Internal error: canonical prefix \"$prefix\" does not have 4 hextets.\n"
        unless (@hextets == 4);

    my $h123 = _ipv6_norm (join (':', @hextets[0..2])); # canonical: lowercase, no leading zeros
    my $h4   = hex ($hextets[3]);
    my $h4top = $h4 & _ipv6_h4_prefix_mask ($len);   # zero the host bits

    return ($h123, $h4top);
}

# Normalize "h1:h2:h3:h4" hextets (lowercase, no leading zeros) for comparison.
sub _ipv6_norm {
    my ($body) = @_;
    return (join (':', map { sprintf ('%x', hex ($_)) } split (/:/, $body)));
}

# Subroutine to obtain an IPv6 prefix from a file such as a dhcp6leased file (/var/db/dhcp6leased/<interface-name>).
# Format can also be a CIDR-format IPv6 prefix.
# Assumes 1-4 characters per hextet and four hextets.
sub _custom_get_prefix_delegation {
    my ($file) = @_;

    open (my $fh, '<', $file) || die "Cannot open prefix delegation file $file. $!\n";
    my $prefix = <$fh>;
    close ($fh);
    chomp ($prefix);

    my $prefix_len;
    # dhcp6leased file, we only look at the first delegated prefix.
    if ($prefix =~ /^ia_pd \d ((?:[0-9a-fA-F]{1,4}:){3}[0-9a-fA-F]{1,4}::) (\d{2})$/) {
	$prefix = "$1/$2";
	$prefix_len = $2;
    }
    elsif ($prefix =~ /^(?:[0-9a-fA-F]{1,4}:){3}[0-9a-fA-F]{1,4}::\/(\d{2})$/) {
	$prefix_len = $1; # just capture length, $prefix is OK if the length is OK.
    }
    else {
	die "Cannot extract valid prefix from prefix file $file, just \"$prefix\".\n";
    }

    die "Invalid prefix length $prefix_len, must be 56 or 60. $prefix\n" unless ($prefix_len == 56 || $prefix_len == 60);

    return $prefix;
}

# Numeric helpers for hextet-4 prefix logic. A /56 prefix occupies the top
# 8 bits of hextet 4; a /60, the top 12 bits. The remaining low bits are
# host/subnet and must be preserved when rewriting an embedded address.
sub _ipv6_h4_prefix_mask {
    my ($len) = @_;                 # 56 or 60
    my $prefix_bits_in_h4 = $len - 48;      # 8 for /56, 12 for /60
    return (0xFFFF << (16 - $prefix_bits_in_h4)) & 0xFFFF;
}

# Substitute the old IPv6 prefix with the new one in $file.
# Two passes: bare CIDR prefixes (rewrite prefix bits AND /NN), then
# prefixes embedded in full addresses (rewrite prefix bits, preserve host bits).
# $old_h123/$new_h123 : canonical hextets 1-3, e.g. "2001:db8:ab"
# $old_h4top/$new_h4top: hextet-4 value with only prefix bits set (host bits 0)
# $old_len/$new_len    : 56 or 60
sub _custom_ipv6_substitute_in_file {
    my ($file, $old_h123, $old_h4top, $old_len,
                $new_h123, $new_h4top, $new_len) = @_;

    my $old_mask      = _ipv6_h4_prefix_mask ($old_len);
    my $new_mask      = _ipv6_h4_prefix_mask ($new_len);
    my $new_host_mask = (~$new_mask) & 0xFFFF;
    my $newly         = $new_mask & ~$old_mask & 0xFFFF;  # prefix-under-new, host-under-old
    my $changed = 0;

    my $bak = "$file.bak";
    rename ($file, $bak) || die "Cannot rename $file to $bak. $!\n";
    open (my $in,  '<', $bak)  || die "Cannot open $bak. $!\n";
    open (my $out, '>', $file) || die "Cannot open $file. $!\n";
    # Keep the source file's mode (see _custom_global_replace_in_file).
    my $mode = (stat ($in))[2] & 07777;
    chmod ($mode, $out) || die "Cannot set mode on $file. $!\n";

    while (my $line = <$in>) {
        my $before = $line;

        # PASS 1: the bare delegation CIDR itself (::/oldlen exactly).
        ($line =~ s{
            \Q$old_h123\E : ([0-9a-fA-F]{1,4}) :: / $old_len (?![0-9])
        }{
            my $h4 = hex ($1);
            (($h4 & $old_mask) == $old_h4top)
              ? sprintf ("%s:%x::/%d", $new_h123, $new_h4top, $new_len)
              : $&;
        }gexi);

        # PASS 1b: in-prefix CIDRs LONGER than the delegation (e.g. /64s under
        # the /60). Rewrite the delegation prefix bits, preserve the
        # sub-delegation bits (which /64) and the /NN length. On a narrowing
        # transition, a /64 whose now-prefix bits fall outside the new
        # delegation is orphaned -> warn and leave verbatim.
        ($line =~ s{
            \Q$old_h123\E : ([0-9a-fA-F]{1,4}) :: / (\d+) \b
        }{
            my ($h4, $nn) = (hex ($1), $2);
            if    ($nn <= $old_len)                        { $&; }
            elsif (($h4 & $old_mask) != $old_h4top)        { $&; }
            elsif (($h4 & $newly) != ($new_h4top & $newly)) {
                warn sprintf ("Orphaned /%d under prefix: %s:%x::/%d falls outside "
                            . "new /%d delegation; left unchanged.\n",
                              $nn, $old_h123, $h4, $nn, $new_len);
                $&;
            }
            else {
                my $sub = $h4 & $new_host_mask;
                sprintf ("%s:%x::/%d", $new_h123, ($new_h4top | $sub), $nn);
            }
        }gexi);

        # PASS 2: prefix embedded in a full address.
        ($line =~ s{
            \Q$old_h123\E : ([0-9a-fA-F]{1,4}) \b (?! :* / \d)
        }{
            my $h4 = hex ($1);
            # Only addresses inside the old delegation are rewritten (or
            # can be orphaned); others sharing hextets 1-3 are left alone.
            # Before 1.9 the orphan check ran first and could die on them.
            if (($h4 & $old_mask) != $old_h4top) {
                $&;
            }
            elsif (($h4 & $newly) != ($new_h4top & $newly)) {
                die sprintf ("Address hextet-4 %#x has subnet bits that would be "
                           . "lost narrowing /%d -> /%d; manual renumbering required.\n",
                             $h4, $old_len, $new_len);
            }
            else {
                sprintf ("%s:%x", $new_h123, ($new_h4top | ($h4 & $new_host_mask)));
            }
        }gexi);

        $changed++ if ($line ne $before);
        print $out $line;
        if ($line eq $before && $line =~ /\Q$old_h123\E:/i) {
            warn "Coverage: $file line $.: contains prefix $old_h123 but no "
               . "substitution fired (spelling? length mismatch?): $line";
        }
    }
    close ($in);
    close ($out) || die "Error writing $file. $!\n";
    unlink ($bak);
    return $changed;
}

### End custom packages.

# Subroutine to add any new syslock groups from config file entries.
sub add_syslock_groups {
    my ($config_syslock_groups, @syslock_groups) = @_;
    my ($syslock_group);

    foreach $syslock_group (@{$config_syslock_groups}) {
	push (@syslock_groups, $syslock_group) unless (grep { $_ eq $syslock_group } @syslock_groups);
    }
    
    return (@syslock_groups);
}

# Subroutine to create syslock group file.
sub create_syslock_group_file {
    my ($file, @syslock_groups) = @_;
    my $syslock_group;

    open (my $syslock_group_fh, '>', $file) || die "Cannot open $file for writing. $!\n";
    foreach $syslock_group (@syslock_groups) {
	print $syslock_group_fh "$syslock_group\n";
    }
    close ($syslock_group_fh);
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

# This differs in install.pl.
sub can_accept_alternate_plain_key {
    my ($key_file) = @_;
    print "Plain/custom signed with non-domain key: $key_file (rejected)\n";
    return 0;
}
