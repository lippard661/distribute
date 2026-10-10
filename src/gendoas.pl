#!/usr/bin/perl
# Script to use comments to generate doas.conf files for specific hosts
# from a template file.

# Written 12 August 2019 by Jim Lippard
# Modified 10 February 2026 by Jim Lippard to use perl modules for temp file,
#    do some minor cleanup, add pledge/unveil, add -o and -V options.
# Modified 20 April 2026 by Jim Lippard to fix -V output.
# Modified 2 May 2026 by Jim Lippard to use block eq greps, do better error checking,
#    remove tmppath pledge.
# Modified 18 May 2026 by Jim Lippard to remove bareword filehandles, only use
#    pledge/unveil on OpenBSD, and reject non-commented lines after Gemini review.
# Modiied 1 July 2026 by Jim Lippard for some minor cleanup after Claude
#    Opus 4.8 review.
# Modified 10 October 2026 by Claude Opus 5.5 at the direction of Jim Lippard
#    (version 1.6): -o is now always respected, including for this host
#    (previously generating for this host ignored -o and overwrote
#    /etc/doas.conf, which made distribute.pl unable to stage this host's
#    doas.conf); /etc/doas.conf is only written when no -o is given and the
#    target is this host. Also: die on more than one host argument
#    (previously extras were ignored and this host's live file was
#    rewritten); check the copy for -o/other-host output; don't require an
#    existing /etc/doas.conf to back up; set the output mode explicitly
#    (live file keeps its existing mode, new files are 0600) instead of
#    taking the umask; check the generated file with doas -C before
#    installing or writing it; get the date before unveil so the header
#    uses local time rather than UTC; die if the template ends inside a
#    continuation.

use strict;
use warnings;
use File::Basename qw( basename dirname );
use File::Copy;
use File::Spec;
use Getopt::Std;
use if $^O ne 'openbsd', 'File::Temp', qw( :mktemp );
use if $^O eq 'openbsd', 'OpenBSD::MkTemp', qw( mkdtemp );
use if $^O eq 'openbsd', 'OpenBSD::Pledge';
use if $^O eq 'openbsd', 'OpenBSD::Unveil';
use Sys::Hostname;

my $ME = 'gendoas';

my $TEMPLATE = '/etc/doas.conf.template';
my $OUTPUT_FILE = 'doas.conf';
my $CONFIG_FILE = '/etc/doas.conf';
my $BACKUP_CONFIG_FILE = '/etc/doas.conf.bak';
my $DOAS = '/usr/bin/doas';
$DOAS = '/usr/local/bin/doas' if (!-x $DOAS && -x '/usr/local/bin/doas');
my $NEW_FILE_MODE = 0600;

my (%options, $output_file, $another_host, $write_live, $hostname, $user, $date,
    $temp_dir, $host_match, $all_except, $host_list, @host_array, $mode);
my $continuation_line = 0;

# END block to cleanup temp files.
END { if (defined $temp_dir && -d $temp_dir) { unlink "$temp_dir/$OUTPUT_FILE"; rmdir $temp_dir; } }

# Use: gendoas.pl [-V|-o output file] [host]

getopts ('Vo:', \%options) || exit;

if ($options{'V'}) {
    print "gendoas.pl version 1.6 of 10 October 2026\n";
    exit;
}

die "Usage: gendoas.pl [-V|-o output file] [host]\n" if (@ARGV > 1);

$output_file = $options{'o'} || $OUTPUT_FILE;

my $abs_output = File::Spec->canonpath(File::Spec->rel2abs($output_file));
my $abs_dir = dirname($abs_output);

die "Cannot write under /etc with -o; run without -o to update /etc/doas.conf.\n"
    if ($abs_dir eq '/etc' || $abs_dir =~ m{^/etc/});

my $full_hostname = hostname() || die "Hostname is undefined.\n";
(my $short_hostname, my $domain) = split (/\./, $full_hostname, 2);

if (@ARGV == 1) {
    $hostname = $ARGV[0];
    $another_host = ($hostname eq $short_hostname) ? 0 : 1;
}
else {
    $hostname = $short_hostname;
    $another_host = 0;
}

# Install over /etc/doas.conf only for this host and only without -o.
# With -o (e.g. distribute.pl staging this host's doas.conf for
# install.pl), always write the requested file and leave /etc alone.
$write_live = (!$another_host && !defined ($options{'o'}));

# Before unveil, which hides /usr/share/zoneinfo (localtime would be UTC).
$user = getpwuid($<) // $<;
$date = localtime (time());

## Pledge and unveil. (OpenBSD only)
if ($^O eq 'openbsd') {
    # proc/exec for the doas -C syntax check.
    pledge ('rpath', 'wpath', 'cpath', 'fattr', 'getpw', 'proc', 'exec', 'unveil') || die "Cannot pledge promises. $!\n";

    unveil ($TEMPLATE, 'r');
    unveil ('/tmp', 'rwc');
    unveil ($DOAS, 'rx');
    if ($write_live) {
	# Need to create or overwrite the doas.conf on this host.
	unveil ('/etc', 'rwc');
	unveil ($CONFIG_FILE, 'rwc');
    }
    else {
	unveil ($abs_dir, 'rwc');
	unveil ($abs_output, 'rwc');
    }
    unveil ();
}

# Open template.
open (my $template_fh, '<', $TEMPLATE) || die "Cannot open template $TEMPLATE. $!\n";

# Open tempfile.
$temp_dir = mkdtemp ("/tmp/$ME.XXXXXXXX") || die "Cannot create temp dir. $!\n";
chomp ($temp_dir);
open (my $output_fh, '>', "$temp_dir/$OUTPUT_FILE") || die "Cannot open $temp_dir/$OUTPUT_FILE. $!\n";

$host_match = 1;

print $output_fh "# doas.conf for $hostname created with $ME by user $user on $date.\n";

# Read template, write temp file.
while (<$template_fh>) {
    if (/^\s*#\s*hosts:\s*(.*$)/) {
	$all_except = 0;
	$host_list = $1;
	if ($host_list eq 'none') {
	    $host_match = 0;
	    next;
	}
	elsif ($host_list eq 'all') {
	    $host_match = 1;
	    print $output_fh "$_";
	}
	else {
	    if ($host_list =~ /^all except\s*(.*$)/) {
		$all_except = 1;
		$host_list = $1;
	    }
	    # Check for match to current host.
	    @host_array = split (/ /, $host_list);
	    if ((!$all_except && grep { $_ eq $hostname } @host_array) ||
		($all_except && !grep { $_ eq $hostname } @host_array)) {
		$host_match = 1;
		print $output_fh "$_";
	    }
	    else {
		$host_match = 0;
	    }
	}
    }
    elsif (/^\s*#\s*(deny|permit)(.*$)/) {
	# Commented line with deny/permit. If host_match, then we remove the comment.
	# Otherwise, we omit it.
	print $output_fh "$1$2\n" if ($host_match);
	# If the line ends with a \, then we continue comment removal on subsequent lines.
	$continuation_line = 1 if ($2 =~ /\\$/);
    }
    elsif ($continuation_line) {
	$continuation_line = 0 if (!/\\$/);
	if (/^\s*#(.*$)/) {
	    print $output_fh "$1\n" if ($host_match);
	}
	else {
	    chomp(my $line = $_);
	    die "Template error at line $.: continuation line is not commented: $line\n";
	}
    }
    elsif (/^\s*#/ || /^\s*$/) {
        # Comment or blank line - pass through if host_match
        print $output_fh "$_" if ($host_match);
    }
    else {
	chomp(my $line = $_);
        die "Template error at line $.: line is not commented: $line\n";
    }
}
die "Template error: template ends inside a continuation line.\n" if ($continuation_line);
close ($output_fh) || die "Error writing $temp_dir/$OUTPUT_FILE. $!\n";
close ($template_fh);

# Syntax-check the result before it goes anywhere; a broken doas.conf
# can lock out root access. (doas -C parses the file and exits.)
if (-x $DOAS) {
    system ($DOAS, '-C', "$temp_dir/$OUTPUT_FILE");
    die "Could not run $DOAS -C. $!\n" if ($? == -1);
    die "Generated doas.conf for $hostname fails $DOAS -C syntax check; not written.\n" if ($? != 0);
}
else {
    print "Note: $DOAS not found, generated doas.conf not syntax checked.\n";
}

if ($write_live) {
    # Keep the live file's mode (new file: $NEW_FILE_MODE). Create backup
    # if there is an existing file, copy temp file over original.
    if (-e $CONFIG_FILE) {
	$mode = (stat ($CONFIG_FILE))[2] & 07777;
	copy ($CONFIG_FILE, $BACKUP_CONFIG_FILE)
	    || die "Cannot create backup: $!\n";
	chmod ($mode, $BACKUP_CONFIG_FILE) || die "Cannot set mode on $BACKUP_CONFIG_FILE: $!\n";
    }
    else {
	$mode = $NEW_FILE_MODE;
    }
    copy ("$temp_dir/$OUTPUT_FILE", "$CONFIG_FILE.new")
	|| die "Cannot copy new file: $!\n";
    chmod ($mode, "$CONFIG_FILE.new") || die "Cannot set mode on $CONFIG_FILE.new: $!\n";
    rename ("$CONFIG_FILE.new", $CONFIG_FILE)
	|| die "Cannot rename new file over old file: $!\n";
}
else {
    # Another host, or -o given: put it where requested (-o) or in the
    # current directory.
    copy ("$temp_dir/$OUTPUT_FILE", $output_file)
	|| die "Cannot copy generated doas.conf to $output_file: $!\n";
    chmod ($NEW_FILE_MODE, $output_file) || die "Cannot set mode on $output_file: $!\n";
}

# Remove temp file and temp dir (done by END block above).
