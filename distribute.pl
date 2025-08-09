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

use strict;
use Archive::Tar;
use File::Basename qw(basename dirname fileparse);
use File::Copy qw(copy cp);
use File::Path qw(rmtree);
use Getopt::Std;
use IO::Uncompress::Gunzip;
use POSIX qw(strftime);
use Signify qw(signify_error);
use Sys::Hostname;
use if $^O eq "openbsd", "OpenBSD::MkTemp", qw( mkdtemp );
use if $^O eq "openbsd", "OpenBSD::Pledge";
use if $^O eq "openbsd", "OpenBSD::Unveil";


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
my $MKTEMP = '/usr/bin/mktemp';
my $RSYNC = '/usr/local/bin/rsync';
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
my $current_openbsd = `$UNAME -a`;
$current_openbsd =~ s/^OpenBSD [\w\.]+ (\d+)\.(\d+) .*$/$1$2/;
$current_openbsd--; 
my $OPENBSD_MIN_VERSION = "$current_openbsd";

my $CONFIG_FILE = '/etc/distribute.conf';

my %CONFIG; # was constant, now is generated by parse_config
my @HOSTS; # was constant, now generated by parse_config

### For custom files. Add any new required pledges to the hash
### %CUSTOM_PLEDGE for the , they will only be pledged when that
### file is being distributed.

my @custom_pledges;

# for ip-address:
# fattr for copy of pf.conf to preserve perms, doesn't seem to work
my %CUSTOM_PLEDGE = ('ip-address' => [ 'dns', 'fattr' ] );

### Variables.

my (%opts, $use_v6, $use_prev_year_key, $rsync_host_suffix, $config_file,
    $host_option, @selected_hosts, $debug_flag);

my ($arg, @args, $file, @files, $package_path,
    %host_package_path, %host_package_files,
    $host, $date, $temp_dir, $temp_file,
    $dest_path, $dest_dir, $dest_file,
    $have_fake_dir,
    $signify_passphrase, @files_to_ship_and_remove, @rsync_file_list,
    @install_packages);

# Hash of arrays, one per host.
my %syslock_groups;

# Signify errors.
my @errors;

# Maybe my source code should be in a CVS repo on hagbard as the authoritative
# location?
# 1. Identify files to distribute. (Command line, config file?)
#       How to determine where they go? Could be complicated, especially, e.g.,
#       doas.conf.host. Maybe hard code types, so that command is just
#       "distribute.pl doas.conf reportnew.conf [other signed packages?]"
# 2. Package them up. (Signed gzip tar file, package-host-yyyymmddhhmm.tgz,
#            one per host with the appropriate content for each.)
#      Could bundle up files to install with appropriate dir structure and
#       filenames for ultimate location.
#      For signed packages (sigtree etc.) the packages can just go as-is
#       and there's not much to be gained by zipping them again.
#      Source could be in its defined location or not, if not, it needs
#      to either be in the config or specified (either fake dir structure
#      in gzip, or specified in an additional file in the gzip).
#      Need to assemble the list of files, then tar zip them all up.
# 3. Send them over. (Use rsnapshot method--put them in /var/install.)
#    rsync --rsync-path=/usr/local/sbin/rsync_wrapper.sh -avr /var/install/host/* host-rsnapshot:/var/install
#     Note that source can also be /var/install on hagbard to simplify
#   Could just use existing rsync-tools, but it complicates things
# Add some kind of PLIST file for /etc/CHANGELOG.
#
# Install script:
# (run via rc.shutdown? but needs to be after securelevel changes)
# (could be during startup, but will need to add this script to the list
# of what has to be immutable to avoid security bypasses)
# 4. Securelevel check.
# 5. Look for packages.
# 6. Verify signature. signify -Vz -p /etc/signify/<domain>-<year>-pkg.pub
# 7. Change flags where necessary for contents (can use sysunlock).
# 8. Install. maybe verify again: signify -Vz -p /etc/signify/<domain>-<year>-pkg.pub | tar ztf - (use tar to install?) yes.
# 9. Re-lock.
# 10. Update CHANGELOG.

### Main program.

# Get options first.
getopts ('46pdc:h:', \%opts) || exit;

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
    die "Usage: distribute.pl [-4|-6|-p (prior year key)|-c config|-h hosts(CSV)|-d debug] [files]\n";
}

# Parse config file.
&parse_config ($config_file);

# Validate.
foreach $arg (@ARGV) {
    die "Unknown file. $arg\n" if (!defined ($CONFIG{$arg}));
    die "Error in config. Undefined TYPE \"$CONFIG{$arg}{TYPE}\".\n" if (!grep (/^$CONFIG{$arg}{TYPE}$/, @TYPES));
    push (@files, $arg);
    if ($CONFIG{$arg}{TYPE} eq 'custom') {
	push (@custom_pledges, $CUSTOM_PLEDGE{$arg}) if ($CUSTOM_PLEDGE{$arg});
    }
}

# Validate @selected_hosts;
if ($opts{'h'}) {
    foreach $host (@selected_hosts) {
	die "-h $opts{'h'} specifies host not defined in config. $host\n" if (!grep(/^$host$/, @HOSTS));
    }
}

# Get the date (YYMMDD-HHMMSS).
$date = strftime ("%Y%m%d-%H%M%s", localtime (time()));

# Use pledge and unveil.
# Already got the date so don't need /usr/share/zoneinfo.
if ($^O eq 'openbsd') {
    my ($dir);
    
    # pledge. stdio already included.
    pledge ('rpath', 'wpath', 'cpath', 'tmppath', 'exec', 'proc', 'fattr', 'unveil', @custom_pledges);

    # unveil, need read-only for all source locations, read-write-create
    # for destination locations, and read-execute for all commands used.
    # For plain files, get the dirname from path. For packages, they all
    # come from PKG_DIR. For custom -- special cased.
    foreach $file (@files) {
	if ($CONFIG{$file}{TYPE} eq 'plain') {
	    $dir = dirname ($CONFIG{$file}{FILE});
#	    die "Cannot unveil $dir for plain file $file. $!\n" if (!-d $dir);
	    unveil ($dir, 'r');
	}
	elsif ($CONFIG{$file}{TYPE} eq 'custom') {
	    my $unveil_file;
	    if (defined ($CONFIG{$file}{UNVEIL})) {
		foreach $unveil_file (@{$CONFIG{$file}{UNVEIL}}) {
#		    die "Cannot unveil $unveil_file from \"unveil:\" for file $file. $!\n" if (!-e $unveil_file);
		    unveil ($unveil_file, 'r');
		}
	    }
	    if (defined ($CONFIG{$file}{UNVEILEXEC})) {
		foreach $unveil_file (@{$CONFIG{$file}{UNVEILEXEC}}) {
#		    die "Cannot unveil $unveil_file from \"unveil-exec:\" for file $file. $!\n" if (!-e $unveil_file);
		    unveil ($unveil_file, 'rx');
		}
	    }
	}
    }
    unveil ($PKG_DIR, 'r');

    # unveil commands.
    # removed $MKTEMP.
    unveil ($MKDIR, 'rx');
    unveil ($RSYNC, 'rx');
    unveil ($SIGNIFY, 'rx');
    unveil ($STTY, 'rx');

    # Signify keys.
    unveil ($SIGNIFY_PUB_KEY_DIR, 'r');

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
if ($^O eq 'openbsd') {
    $temp_dir = mkdtemp ('/tmp/distribute.XXXXXXX');
}
else {
    $temp_dir = `$MKTEMP -d -q /tmp/distribute.XXXXXXX`;
    chomp ($temp_dir);
}

foreach $file (@files) {
    print "DEBUG: processing file $file\n" if ($debug_flag);
    # Convert 'all' to the hosts list. Does not include hagbard.
    $CONFIG{$file}{HOSTS} = \@HOSTS if ($CONFIG{$file}{HOSTS}[0] eq 'all');

    print "DEBUG: \@{\$CONFIG{\$file}{HOSTS}} = @{$CONFIG{$file}{HOSTS}}\n" if ($debug_flag);
    print "DEBUG: \@selected_hosts = @selected_hosts\n" if ($debug_flag && $host_option);
    # Accumulate syslock groups.
    foreach $host (@{$CONFIG{$file}{HOSTS}}) {
	next if ($host_option && !grep (/^$host$/, @selected_hosts));
	print "DEBUG: processing host $host\n" if ($debug_flag);
	(@{$syslock_groups{$host}}) = &add_syslock_groups ($CONFIG{$file}{SYSLOCKGROUPS}, @{$syslock_groups{$host}});
    }

    if ($CONFIG{$file}{TYPE} eq 'package') {
	# Look for most up-to-date package in $PKG_DIR.
	$package_path = &find_package ($PKG_DIR, $CONFIG{$file}{FILE});
	# Verify signature.
	if (!&verify_signature ($package_path)) {
	    die "Invalid or missing signature. $package_path\n";
	}
	# Copy package to install directories.
	# We put these into host_package_path so they get shipped, but
	# not into host_package_files which get signed.
	@install_packages = &copy_package ($package_path, @{$CONFIG{$file}{HOSTS}});

	push (@files_to_ship_and_remove, @install_packages);
	# It's not dest_file or dest_dir in this case, it's just the
	# package filename, so we can add it to host_package_path so
	# that it gets shipped.
	($dest_file, $dest_dir) = fileparse ($package_path);
	foreach $host (@{$CONFIG{$file}{HOSTS}}) {
	    $host_package_path{$host} = "$INSTALL_DIR/$host/$dest_file";
	}
    }
    elsif ($CONFIG{$file}{TYPE} eq 'plain') {
	# Make sure file exists.
	die "File in config can't be found. $! $CONFIG{$file}{FILE}\n" if (!-e $CONFIG{$file}{FILE});

	# If the destination is different from the source (DEST is used),
	# set up fake temp dir. (Need separate fake temp dir for each host
	# just in case some files are generated or otherwise different per
	# host.)
	if ($CONFIG{$file}{DEST}) {
	    $dest_path = $CONFIG{$file}{DEST};
	    ($dest_file, $dest_dir) = fileparse ($dest_path);
	    $dest_path = substr ($dest_path, 1, length ($dest_path) - 1);
	    foreach $host (@{$CONFIG{$file}{HOSTS}}) {
		# Make the fake directory (per-host).
		&make_fake_dir ($temp_dir, $dest_dir, $host);
		# Copy the file into it. Preserve permissions.
		cp ($CONFIG{$file}{FILE}, "$temp_dir/$host/$dest_path");
	    }
	    $have_fake_dir = 1;
	}
	else {
	    $dest_path = $CONFIG{$file}{FILE};
	}
	# Add to file to package list.
	foreach $host (@{$CONFIG{$file}{HOSTS}}) {
	    push (@{$host_package_files{$host}}, $dest_path);
	}
    }
    elsif ($CONFIG{$file}{TYPE} eq 'custom') {
	# Make sure file exists. (Ignore filenames with commas.)
	# With commas should probably split it out and check for all, but
	# will have to do $HOST substitution and check all relevant
	# instances.
	die "File in config can't be found. $! $CONFIG{$file}{FILE}\n" if (!-e $CONFIG{$file}{FILE} && $CONFIG{$file}{FILE} !~ /,/);

	# Each is separate, for now. There may end up being some different
	# custom types that have common features.
	if ($file eq 'doas.conf') {
	    &_custom_doas_dot_conf ($temp_dir, $CONFIG{$file}{CUSTOMVARS}, $CONFIG{$file}{DEST}, @{$CONFIG{$file}{HOSTS}});
	    $have_fake_dir = 1;
	}
	# Change old IP address to new IP address in a list of files for
	# distribution to fnord and nkrumah (see config).
	# Dest dirs are pulled from config:
	# /etc, /etc/mail, /home/_rsyncu/.ssh
	# This does not change /etc/faild.conf for hagbard.
	elsif ($file eq 'ip-address') {
	    &_custom_ip_address ($temp_dir, $CONFIG{$file}{CUSTOMVARS}, $CONFIG{$file}{FILE}, $CONFIG{$file}{DEST}, @{$CONFIG{$file}{HOSTS}});
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
if (%host_package_files) {
    $signify_passphrase = &get_signify_passphrase;
}

# If there were any plain or custom files, create and sign the gzips, then copy
# the packages to the install directory.
foreach $host (keys (%host_package_files)) {
    $host_package_path{$host} = &create_package ($have_fake_dir, $temp_dir, $date, $host, @{$host_package_files{$host}});
    if (!$use_prev_year_key && !Signify::sign_gzip ($host_package_path{$host}, $signify_passphrase, $SIGNIFY_SEC_KEY, $temp_dir)) {
	my @errors = Signify::signify_error;
	die "@errors";
    }
    elsif ($use_prev_year_key && !Signify::sign_gzip ($host_package_path{$host}, $signify_passphrase, $PRIOR_SIGNIFY_SEC_KEY, $temp_dir)) {
	my @errors = Signify::signify_error;
	die "@errors";
    }

    push (@files_to_ship_and_remove, &copy_package ($host_package_path{$host}, $host));

    # Create syslock group file if any syslock groups are specified.
    if (@{$syslock_groups{$host}}) {
	&create_syslock_group_file ("$host_package_path{$host}.grp", @{$syslock_groups{$host}});
	# Sign it.
	if (!$use_prev_year_key && !Signify::sign ("$host_package_path{$host}.grp", $signify_passphrase, $SIGNIFY_SEC_KEY)) {
	    @errors = Signify::signify_error;
	    die "Could not sign syslock group file $host_package_path{$host}.grp @errors";
	}
	elsif ($use_prev_year_key && !Signify::sign ("$host_package_path{$host}.grp", $signify_passphrase, $PRIOR_SIGNIFY_SEC_KEY)) {
	    @errors = Signify::signify_error;
	    die "Could not sign syslock group file $host_package_path{$host}.grp @errors";
	}   
	# Add both syslock group file and signature to @files_to_ship_and_remove.
	push (@files_to_ship_and_remove, &copy_package ("$host_package_path{$host}.grp", $host));
	push (@files_to_ship_and_remove, &copy_package ("$host_package_path{$host}.grp.sig", $host));
    }
}

# Now actually distribute the packages to the destinations.
# Instead of doing one at a time we could ship all at once, which
# might be a lot nicer. Would need to find all the matches and add
# them to the command line list, then use the same list to unlink
# them.
foreach $host (keys (%host_package_path)) {
    @rsync_file_list = ();
    foreach $package_path (@files_to_ship_and_remove) {
	if ($package_path =~ /^\/var\/install\/$host\//) {
	    push (@rsync_file_list, $package_path);
	    # With rsync_wrapper.sh	    
	    # system ("$RSYNC --rsync-path=/usr/local/sbin/rsync_wrapper.sh -avr $package_path $host-rsnapshot:/var/install/");
	    # With rrsync: the authorized_keys file forces rrsync -doas /var/install.
	}	    
    }
    print "Distributing to $host.\n";
    system ($RSYNC, '-avr', @rsync_file_list, "$host$rsync_host_suffix:.");
}

# Now clean it all up and delete them.
foreach $file (@files_to_ship_and_remove) {
    unlink ($file);
}

# Exit temp subdir, but stay in /tmp.
chdir ('/tmp');

# Remove the fake dirs if we're done with them. (Superfluous.)
#if ($have_fake_dir) {
#    rmtree ("$temp_dir/$file");
#}

# Delete temp dir.
rmtree ($temp_dir);

### Subroutines.

# Subroutine to parse config file.
sub parse_config {
    my ($config_file) = @_;

    my ($context);
    my $GLOBAL_CONTEXT = 1;
    my $FILE_CONTEXT = 2;
    
    my ($line_no, @host_list, @syslock_groups_list,
	$field, $value, $current_name,
	@syslock_groups, $group, @hosts, $host);
    my ($got_file, $got_dest, $got_type, $got_syslock_groups, $got_hosts);
    my (%macros, $macro_name, $have_macros, $more_to_process);

    $line_no = 0;
    $context = $GLOBAL_CONTEXT;

    open (FILE, '<', $config_file) || die "Cannot open config file $config_file. $!\n";
    while (<FILE>) {
	chomp;
	$line_no++;
	if (/^\s*#|^\s*$/) {
	    # ignore
	}
	# Macro definition. Can occur anywhere so long as definition is before use.
	elsif (/^([\w0-9-_]+)\s*=\s*\"([\S ]+)\"$/) {
	    $field = $1;
	    $value = $2;
	    die "Macro \"$field\" defined a second time on line $line_no. $_\n" if (defined ($macros{$field}));
	    $macros{$field} = $value;
	    $have_macros = 1;
	}
	elsif (/\s*([\w-]+):\s*(.*)$/) {
	    $field = $1;
	    $value = $2;

	    # any macros to expand?
	    $more_to_process = 1;
	    while ($have_macros && $more_to_process) {
		if ($value =~ /%%([\w0-9-_]+)%%/) {
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
		push (@HOSTS, @host_list); # global like %CONFIG
	    }
	    elsif ($field eq 'syslock-groups-list') {
		die "A \"syslock-groups-list:\" field in file context on lin $line_no. $_\n" if ($context == $FILE_CONTEXT);
		die "A second \"syslock-groups-list:\" field on line $line_no. $_\n" if (@syslock_groups_list);
		@syslock_groups_list = split (/,\s*/, $value);
	    }
	    elsif ($field eq 'name') {
		if ($context == $GLOBAL_CONTEXT) {
		    die "No \"host-list:\" defined before first \"name:\" field on line $line_no. $_\n" unless (@host_list);
		    $context = $FILE_CONTEXT;
		}
		if (defined ($current_name)) {
		    # Did we get required fields for previous? Also need to check this at end of file for the last one.
		    die "No \"file:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_file);
		    die "No \"type:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_type);
		    die "No \"syslock-groups:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_syslock_groups && $CONFIG{$current_name}{TYPE} ne 'package' && @syslock_groups_list); # optional for packages, or for everything if no syslock-groups-list defined.
		    die "No \"hosts:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_hosts);
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
		$CONFIG{$current_name}{DEST} = $value;
		$got_dest = 1; # optional; forbidden for package type
		if ($got_type && $CONFIG{$current_name}{TYPE} eq 'package') {
		    die "A \"dest:\" field is not permitted for \"package\" type file \"$current_name\" on line $line_no. $_\n";
		}
	    }
	    elsif ($field eq 'type') {
		die "A \"type:\" field in global context on line $line_no. $_\n" if ($context == $GLOBAL_CONTEXT);
		die "A second \"type:\" for $current_name on line $line_no. $_\n" if ($got_type);
		die "Invalid type \"$value\" on line $line_no. $_\n" if (!grep (/^$value$/, @TYPES));
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
		    next if grep (/^$group$/, @syslock_groups_list);
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
		    if ($custom_var =~ /\s*([\w0-1-_]+)\s*=\s*([\S ]+)$/) {
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
		@hosts = split (/,\s*/, $value);
		foreach $host (@hosts) {
		    next if $host eq 'all';
		    next if grep (/^$host$/, @host_list);
		    die "Unknown host \"$host\" in \"hosts:\" field on line $line_no. $_\n";
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
    close (FILE);

    # Did we get required fields for last "name:"? Same checks as at each subsequent "name:" above.
    die "No \"file:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_file);
    die "No \"type:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_type);
    die "No \"syslock-groups:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_syslock_groups);
    die "No \"hosts:\" defined for \"name:\" $current_name before next \"name:\" on line $line_no. $_\n" if (!$got_hosts);
}

# Subroutine to find a package.
sub find_package {
    my ($pkg_dir, $pkg_start) = @_;
    my (@files, $file, $version, $pkg_path);
    my ($major_version, $minor_version, $minor_alpha, $patch_version,
	$check_version,
	$check_major_version, $check_minor_version, $check_minor_alpha, $check_patch_version);

    if ($pkg_start =~ /^(.*)-PKG$/) {
	$pkg_start = $1;
    }
    else {
	die "Error in config. Package filename doesn't end in \"-PKG\". $pkg_start\n";
    }

    opendir (DIR, $pkg_dir) || die "Could not open directory $pkg_dir. $!\n";
    @files = grep (!/^\.{1,2}$/, readdir (DIR));
    closedir (DIR);

    $version = '0.0.0';
    $major_version = '0';
    $minor_version = '0';
    $minor_alpha = '';
    $patch_version = '0';

    foreach $file (@files) {
	if ($file =~ /^$pkg_start-([0-9\w\.]+)\.tgz$/ || $file =~ /^$pkg_start-([0-9\w\.]+-no_[0-9\w]+)\.tgz$/) {
	    # This currently matches python-tkinter-xxx and not just
	    # python-xxx. Is it safe to restrict $1 to numbers, letters,
	    # and periods, and exclude hyphens? i.e., ([0-9\w\.]+)
	    # instead of (.*)?
	    $check_version = $1;
	    ($check_major_version, $check_minor_version, $check_patch_version) = split (/\./, $check_version);
	    $check_minor_version = '0' if (!defined ($check_minor_version));
	    $check_patch_version = '0' if (!defined ($check_patch_version));
	    if ($check_minor_version =~ /^(\d+)([\w]+)$/) {
		$check_minor_version = $1;
		$check_minor_alpha = $2;
	    }
	    if ($check_major_version > $major_version ||
		($check_major_version eq $major_version &&
		 $check_minor_version > $minor_version) ||
		($check_major_version eq $major_version &&
		 $check_minor_version eq $minor_version &&
		 $check_minor_alpha > $minor_alpha) ||
		($check_major_version eq $major_version &&
		 $check_minor_version eq $minor_version &&
		 $check_minor_alpha eq $minor_alpha &&
		 $check_patch_version > $patch_version)) {
		$version = $check_version;
		$major_version = $check_major_version;
		$minor_version = $check_minor_version;
		$minor_alpha = $check_minor_alpha;
		$patch_version = $check_patch_version;
	    }
	}
    }
    die "Could not find $pkg_start package in $PKG_DIR.\n" if (!$version);
    $pkg_path = $PKG_DIR . '/' . $pkg_start . '-' . $version . '.tgz';
    return ($pkg_path);
}

# Subroutine to get signify passphrase.
sub get_signify_passphrase {
    my ($signify_passphrase);
    
    # Get signify passphrase.
    system ($STTY, '-echo');
    print "signify passphrase: ";
    $signify_passphrase = <STDIN>;
    system ($STTY, 'echo');
    chomp ($signify_passphrase);
    return ($signify_passphrase);
}

# Subroutine to sign a gzip file.
sub sign_package {
    my ($signify_passphrase, $temp_dir, $gzip) = @_;

    if (!-r $gzip) {
	die "Could not read $gzip to sign. $!\n";
    }

    # Sign the package.
    open (SIGNIFYPIPE, '|-', "$SIGNIFY -Sz -s $SIGNIFY_SEC_KEY -m $gzip -x $temp_dir/out.tgz") || die "Unable to sign package. $!\n";
    print SIGNIFYPIPE "$signify_passphrase\n";
    close (SIGNIFYPIPE);

    # Copy signed gzip over original.
    copy ("$temp_dir/out.tgz", $gzip);
    
    # Remove extraneous file.
    unlink ("$temp_dir/out.tgz");
}

# Subroutine to copy package to appropriate install dirs.
sub copy_package {
    my ($pkg_path, @hosts) = @_;
    my ($host, $file_basename, @ship_files);

    foreach $host (@hosts) {
	copy ($pkg_path, "$INSTALL_DIR/$host/");
	$file_basename = basename($pkg_path);
	push (@ship_files, "$INSTALL_DIR/$host/$file_basename");
    }
    
    return (@ship_files);
}

# Subroutine to create package tar file for a host. This has to be done
# all at once for a gzipped tar file -- the "r" command won't work.
sub create_package {
    my ($have_fake_dir, $temp_dir, $date, $host, @file_list) = @_;
    my ($pkg_path, $file, $file_wo_slash);

    if ($have_fake_dir) {
	chdir ("$temp_dir/$host");
    }

    $pkg_path = "$temp_dir/$host-$date-package.tgz";

    if (-e $pkg_path) {
	die "Error, $pkg_path already exists.\n";
    }

    # Using the perl module is better than calling system on the command and piping
    # STDERR to /dev/null to avoid the error message about stripping the initial /.
    # The module won't extract with a leading slash so we need to remove them.
    my $tar = Archive::Tar->new;
    $tar->add_files (@file_list);
    foreach $file (@file_list) {
	$file_wo_slash = $file;
	$file_wo_slash =~ s/^\///;
	if (!$tar->rename ($file, $file_wo_slash)) {
	    print "Unable to rename $file to $file_wo_slash in tar file.\n";
	}
    }
    $tar->write ($pkg_path, COMPRESS_GZIP);

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
}

### Custom packages.

# Subroutine to validate custom variables.
sub _custom_validate_custom_vars {
    my ($file, $custom_vars, %req_opt_custom_vars) = @_;
    my (%custom_vars, $custom_var);

    %custom_vars = %{$custom_vars};

    foreach $custom_var (keys (%req_opt_custom_vars)) {
	die "Config is missing required custom variable \"$custom_var\" for $file.\n" if (!defined ($custom_vars{$custom_var}) && $req_opt_custom_vars{$custom_var} eq 'required');
    }

    # Make sure all variables are either required or optional.
    foreach $custom_var (keys (%custom_vars)) {
	die "Config specifies undefined custom variable \"$custom_var\" for $file.\n" if (!grep (/^$custom_var$/, keys (%req_opt_custom_vars)))
    }
}

# Subroutine for custom doas.conf generation and distribution.
sub _custom_doas_dot_conf {
    my ($temp_dir, $custom_vars, $dest_path, @hosts) = @_;
    my (%custom_vars, $dest_file, $dest_dir, $host);
    # global: $have_fake_dir, %host_package_files

    my %REQ_OPT_CUSTOM_VARS = ('gendoas' => 'required');

    &_custom_validate_custom_vars ('doas.conf', $custom_vars, %REQ_OPT_CUSTOM_VARS);

    %custom_vars = %{$custom_vars};

    # required custom vars: gendoas=/path/to/gendoas

    my $PERL = '/usr/bin/perl';
    my $GENDOAS = $custom_vars{'gendoas'};

    die "$! $GENDOAS\n" if (!-e $GENDOAS);

    ($dest_file, $dest_dir) = fileparse ($dest_path);
    $dest_path = substr ($dest_path, 1, length ($dest_path) - 1);
#    $have_fake_dir = 1; # done after call to this subroutine
    foreach $host (@hosts) {
	&make_fake_dir ($temp_dir, $dest_dir, $host);
	chdir ("$temp_dir/$host$dest_dir");
	system ($PERL, $GENDOAS, $host);
	push (@{$host_package_files{$host}}, $dest_path);
    }
}

# Subroutine for custom IP address change.
sub _custom_ip_address {
    my ($temp_dir, $custom_vars, $file, $dest, @hosts) = @_;
    my (%custom_vars, $old_address, $new_address,
	@source_paths, @dest_paths,
	$host, $idx, $source_path, $dest_path);
    # global: $have_fake_dir, %host_package_files
    
    my %REQ_OPT_CUSTOM_VARS = ('wan0' => 'required',
			       'wan1' => 'optional',
			       'wan0-host-fqdn' => 'optional',
			       'wan1-host-fqdn' => 'optional',
			       'ipv6-name' => 'required',
			       'dns' => 'required');

    &_custom_validate_custom_vars ('ip-address', $custom_vars, %REQ_OPT_CUSTOM_VARS);
    
    %custom_vars = %{$custom_vars};

    my $CHMOD = '/bin/chmod';
    
    ($old_address, $new_address) = &_custom_get_old_and_new_ip_addresses ($custom_vars{'wan0-host-fqdn'}, $custom_vars{'wan1-host-fqdn'}, $custom_vars{'ipv6-name'}, $custom_vars{'dns'}, $custom_vars{'wan0'}, $custom_vars{'wan1'});;
    @source_paths = split (/,/, $file);
    @dest_paths = split (/,/, $dest);
#	    $have_fake_dir = 1; done after call to this subroutine
    # I really want to take each corresponding source and dest path
    # to work on for each host as appropriate, so I need to use a
    # for loop instead of foreach.
    foreach $host (@hosts) {
	for ($idx = 0; $idx <= $#source_paths; $idx++) {
	    $source_path = $source_paths[$idx];
	    $dest_path = $dest_paths[$idx];
	    ($dest_file, $dest_dir) = fileparse ($dest_path);
	    $dest_path = substr ($dest_path, 1, length ($dest_path) - 1);
	    # Need to insert $host in middle of source path.
	    # $HOST is special-cased just like $SIGNIFY_PUB_KEY and
	    # $SIGNIFY_PUB_KEY_NEXT (except the latter two are done
	    # at config parse time rather than execution time).
	    if ($source_path =~ /\$HOST/) {
		$source_path =~ s/\$HOST/$host/;
		# Check for source path existence. (Is backup mounted?)
		# Would be better if this were more graceful, cleaned
		# up temp files, or even alternatively used another
		# source (/var/db/servers is available).
		if (!-e $source_path) {
		    die "Source path missing, can use /var/db/servers if urgent: $source_path\n";
		}

		# It doesn't hurt to do this if the dir already exists.
		&make_fake_dir ($temp_dir, $dest_dir, $host);
		# Copy the source file to the destination. -p to
		# preserve permissions. (Doesn't work for pf.conf.)
		cp ($source_path, "$temp_dir/$host/$dest_path");

		# Update the file by changing the IP addresses.
		&_custom_global_replace_in_file ("$temp_dir/$host/$dest_path", $old_address, $new_address);

		# Manually remove g and o read permissions.
		# This must occur AFTER the call to _custom_global_replace_in_file,
		# which creates a new file with default permissions.
		if ($dest_path =~ /\/pf\.conf$/) {
		    system ($CHMOD, 'go-r', "$temp_dir/$host/$dest_path");
		}
		
		push (@{$host_package_files{$host}}, $dest_path);
	    }
	}
    }
}

# Subroutine to get old external IP address from DNS and new
# external IP address via prompt.
# Assumes IPv6 is tunnel over wan0.
sub _custom_get_old_and_new_ip_addresses {
    my ($wan0_host_fqdn, $wan1_host_fqdn, $ipv6_name, $dns, $wan0, $wan1) = @_;
    use Socket qw( :addrinfo SOCK_RAW );
    my ($old_address, $new_address, $wan0_or_wan1,
	$lc_wan0, $lc_wan1, $host_fqdn);
    my ($err);

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
	$wan0_or_wan1 = <STDIN>;
	chomp ($wan0_or_wan1);
	$wan0_or_wan1 =~ tr/A-Z/a-z/;
	$wan0_or_wan1 = 'null' unless ($wan0_or_wan1 eq $lc_wan0 || $wan0_or_wan1 eq $lc_wan1);
    }

    print "Warning: Must manually update /etc/faild.conf and /etc/reportnew/reportnew.conf.\n";
    if ($wan0_or_wan1 eq $lc_wan0) {
	# Assume wan0 has IPv6 tunnel.
	print "Distributing via v4 (default) since v6 tunnel is down.\n";
	print "Warning: Must manually update $ipv6_name tunnel.\n";
	print "Warning: Must manually update firewall tunnel and policies.\n";
	$rsync_host_suffix = $RSYNC_HOST_SUFFIXv4;
	$host_fqdn = $wan0_host_fqdn;
    }
    else { # wan1
	print "Distributing via v6 since v4 address doesn't have access.\n";
	print "Warning: Must manually update DNS record via $dns.\n";
	$rsync_host_suffix = $RSYNC_HOST_SUFFIXv6;
	$host_fqdn = $wan1_host_fqdn;
    }
    if (defined ($host_fqdn)) {
	$old_address = &_get_wan_ip ($host_fqdn);
    }
    else {
	$old_address = 'null';
    }
    while (1) {
	print "Old address: $old_address (return or enter correct): ";
	my $input_string = <STDIN>;
	chomp ($input_string);
	if ($input_string =~ /^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/) {
	    $old_address = $input_string;
	    last;
	}
	elsif ($input_string eq '') {
	    $input_string = $old_address;
	    last;
	}
	else {
	    print "Invalid response \"$input_string\". Enter new IP or hit return.\n";
	}
    }
    
    $new_address = 'null';
    while ($new_address eq 'null') {
    	  print "New IP Address: ";
    	  $new_address = <STDIN>;
    	  chomp ($new_address);
	  $new_address = 'null' if ($new_address !~ /^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$/);
    }
    
    return ($old_address, $new_address);
}

# Subroutine to get WAN IP from fqdn.
sub _get_wan_ip {
    my ($host_fqdn) = @_;
    my ($old_address, $err, @res, $ai);

    ($err, @res) = getaddrinfo ($host_fqdn, "", {socktype => SOCK_RAW});
    if ($err) {
	print "Cannot getaddrinfo - $err";
	$old_address = 'null';
	return ($old_address);
    }
    while ( $ai = shift @res ) {
	($err, $old_address) = getnameinfo($ai->{addr}, NI_NUMERICHOST, NIx_NOSERV);
	if ($err) {
	    print "Cannot getnameinfo - $err";
	    $old_address = 'null';
	    return ($old_address);
	}
    }
    return ($old_address);
}

# Subroutine to do global string replacement on a given file.
sub _custom_global_replace_in_file {
    my ($file, $string, $replace) = @_;
    my $backup_file;

    $backup_file = $file . '.bak';

    rename ($file, $backup_file);
    open (INFILE, '<' . $backup_file) or die "Cannot open file. $backup_file $!\n";
    open (OUTFILE, '>' . $file) || die "Cannot open file for writing. $file $!\n";
    while (<INFILE>) {
	s/$string/$replace/g;
	print OUTFILE $_;
    }
    close (INFILE);
    close (OUTFILE);
    unlink ($backup_file);
}

### End custom packages.

# Subroutine to add any new syslock groups from config file entries.
sub add_syslock_groups {
    my ($config_syslock_groups, @syslock_groups) = @_;
    my ($syslock_group);

    foreach $syslock_group (@{$config_syslock_groups}) {
	push (@syslock_groups, $syslock_group) unless (grep (/^$syslock_group$/, @syslock_groups));
    }
    
    return (@syslock_groups);
}

# Subroutine to create syslock group file.
sub create_syslock_group_file {
    my ($file, @syslock_groups) = @_;
    my $syslock_group;

    open (FILE, '>', $file) || die "Cannot open $file for writing. $!\n";
    foreach $syslock_group (@syslock_groups) {
	print FILE "$syslock_group\n";
    }
    close (FILE);
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
