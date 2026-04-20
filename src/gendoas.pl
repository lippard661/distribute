#!/usr/bin/perl
# Script to use comments to generate doas.conf files for specific hosts
# from a template file.

# Written 12 August 2019 by Jim Lippard
# Modified 10 February 2026 by Jim Lippard to use perl modules for temp file,
#    do some minor cleanup, add pledge/unveil, add -o and -V options.

use strict;
use warnings;
use File::Basename qw( basename dirname );
use File::Copy;
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

my (%options, $output_file, $another_host, $hostname, $user, $date, $temp_dir, $host_match,
    $all_except, $host_list, @host_array, $continuation_line);

# Use: gendoas.pl [-V|-o output file] [host]

getopts ('Vo:', \%options) || exit;

if ($options{'V'}) {
    print 'getopts.pl version 1.1 of 10 February 2026\n';
    exit;
}

$output_file = $options{'o'} || $OUTPUT_FILE;

die "Can't write directly to /etc.\n" if (dirname ($output_file) eq '/etc');

my $full_hostname = hostname() || die "Hostname is undefined.\n";
(my $short_hostname, my $domain) = split (/\./, $full_hostname, 2);

if ($#ARGV == 0) {
    $hostname = $ARGV[0];
    $another_host = 1 unless ($hostname eq $short_hostname);
}
else {
    $hostname = $short_hostname;
    $another_host = 0;
}

## Pledge and unveil.
pledge ('rpath', 'wpath', 'cpath', 'tmppath', 'getpw', 'unveil') || die "Cannot pledge promises. $!\n";

unveil ($TEMPLATE, 'r');
unveil ('/tmp', 'rwc');
unveil (dirname ($output_file), 'rwc');
unveil ($output_file, 'rwc');
if (!$another_host) {
    # Need to create or overwrite the doas.conf on this host.
    unveil ('/etc', 'rwc');
    unveil ($CONFIG_FILE, 'rwc');
}
unveil ();

# Open template.
open (FILE, '<', $TEMPLATE) || die "Cannot open template $TEMPLATE. $!\n";

# Open tempfile.
$temp_dir = mkdtemp ("/tmp/$ME.XXXXXXXX") || die "Cannot create temp dir. $!\n";
chomp ($temp_dir);
open (OUTPUT, '>', "$temp_dir/$OUTPUT_FILE") || die "Cannot open $temp_dir/$OUTPUT_FILE. $!\n";

$host_match = 1;

$user = getpwuid($<);
$date = localtime (time());
print OUTPUT "# doas.conf for $hostname created with $ME by user $user on $date.\n";

# Read template, write temp file.
while (<FILE>) {
    if (/^\s*#\s*hosts:\s*(.*$)/) {
	$all_except = 0;
	$host_list = $1;
	if ($host_list eq 'none') {
	    $host_match = 0;
	    next;
	}
	elsif ($host_list eq 'all') {
	    $host_match = 1;
	    print OUTPUT "$_";
	}
	else {
	    if ($host_list =~ /^all except\s*(.*$)/) {
		$all_except = 1;
		$host_list = $1;
	    }
	    # Check for match to current host.
	    @host_array = split (/ /, $host_list);
	    if ((!$all_except && grep (/^$hostname$/, @host_array)) ||
		($all_except && !grep (/^$hostname$/, @host_array))) {
		$host_match = 1;
		print OUTPUT "$_";
	    }
	    else {
		$host_match = 0;
	    }
	}
    }
    elsif (/^\s*#\s*(deny|permit)(.*$)/) {
	# Commented line with deny/permit. If host_match, then we remove the comment.
	# Otherwise, we omit it.
	print OUTPUT "$1$2\n" if ($host_match);
	# If the line ends with a \, then we continue comment removal on subsequent lines.
	$continuation_line = 1 if ($2 =~ /\\$/);
    }
    elsif ($continuation_line) {
	$continuation_line = 0 if (!/\\$/);
	if (/^\s*#(.*$)/) {
	    print OUTPUT "$1\n" if ($host_match);
	}
	else {
	    print OUTPUT "$_" if ($host_match);
	}
    }
    else {
	# Anything else gets written out if we're in host_match.
	print OUTPUT "$_" if ($host_match);
    }
}
close (OUTPUT);
close (FILE);

if ($another_host) {
    # If we're building a doas.conf for another host, put it in the
    # where requested or in the current directory.
    copy ("$temp_dir/$OUTPUT_FILE", $output_file);
}
else {
    # Create backup, copy temp file over original.
    copy ($CONFIG_FILE, $BACKUP_CONFIG_FILE) && copy ("$temp_dir/$OUTPUT_FILE", $CONFIG_FILE);
}

# Remove temp file and temp dir.
unlink ("$temp_dir/$OUTPUT_FILE");
rmdir ($temp_dir);
