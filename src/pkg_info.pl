#!/usr/bin/perl

# Minimal pkg_info, similar to OpenBSD's without all the options.
# Completely superfluous on OpenBSD, but can be used on Linux or macOS
# in conjunction with install.pl.
# Written 5 October 2025 by Jim Lippard
# Modified 4 January 2026 by Jim Lippard to remove & on subroutine calls.
# Modified 2 May 2026 by Jim Lippard for minor improvements.

use strict;
use warnings;

my $PKG_DIR = '/var/db/pkg';

my ($arg, $package, @all_packages, @found_packages);

if ($#ARGV == -1) {
    list_all_brief();
    exit;
}

@all_packages = get_all_packages();

foreach $arg (@ARGV) {
    $package = find_package ($arg, @all_packages);
    push (@found_packages, $package) if ($package);
}

die "No valid packages specified.\n" unless (@found_packages);

foreach $package (@found_packages) {
    show_package_desc ($package);
}

# Subroutine to get all packages.
sub get_all_packages {
    my (@all_packages);

    opendir (DIR, $PKG_DIR) || die "Cannot open $PKG_DIR for reading file list. $!\n";
    @all_packages = grep (!/^\.{1,2}/, readdir (DIR));
    closedir (DIR);

    return (@all_packages);
}

# Subroutine to find a matching package name.
sub find_package {
    my ($package_string, @all_packages) = @_;
    my $package;

    foreach $package (@all_packages) {
	return ($package) if ($package eq $package_string);
	if ($package =~ /^\Q$package_string\E-\d/) { # must match up to a version number, not just any substring.
	    return ($package);
	}
    }

    print "Did not find matching package for \"$package_string\".\n";
    return 0;
}

sub list_all_brief {
    my (@all_packages, $package, $package_name,
	$one_liner);

    opendir (DIR, $PKG_DIR) || die "Cannot open $PKG_DIR for reading file list. $!\n";
    @all_packages = grep (!/^\.{1,2}$/, readdir (DIR));
    closedir (DIR);

    foreach $package (sort @all_packages) {
	$package_name = 0;
	if (!open (FILE, '<', "$PKG_DIR/$package/+CONTENTS")) {
	    warn "Skipping $package: Cannot open +CONTENTS. $!\n";
	    next;
	}
	while (<FILE>) {
	    if (/^\@name (.*)$/) {
		$package_name = $1;
	    }
	}
	close (FILE);
	die "Cannot find \"\@name\" in +CONTENTS for package $package.\n" unless (defined ($package_name) && length ($package_name) > 0);
	
	open (FILE, '<', "$PKG_DIR/$package/+DESC") || die "Cannot open +DESC for package $package. $!\n";
	$one_liner = <FILE>;
	$one_liner = '' unless defined ($one_liner);
	chomp ($one_liner);
	close (FILE);

	printf "%-19s %s\n", $package_name, $one_liner;
    }
}

sub show_package_desc {
    my ($package) = @_;
    my ($one_liner);
    
    open (FILE, '<', "$PKG_DIR/$package/+DESC") || die "Cannot open +DESC for package $package. $!\n";
    $one_liner = <FILE>;
    chomp ($one_liner);
    print "Information for inst:$package\n\n";
    print "Comment:\n$one_liner\n\nDescription:\n";
    while (<FILE>) {
	chomp;
	print "$_\n";
    }
    close (FILE);

    # Just to be identical to pkg_info.
    print "\n\n";
}
