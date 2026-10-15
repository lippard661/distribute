#!/usr/bin/perl

# Minimal pkg_info, similar to OpenBSD's without all the options.
# Completely superfluous on OpenBSD, but can be used on Linux or macOS
# in conjunction with install.pl.
# Written 5 October 2025 by Jim Lippard
# Modified 4 January 2026 by Jim Lippard to remove & on subroutine calls.
# Modified 2 May 2026 by Jim Lippard for minor improvements.
# Modified 17 May 2026 by Jim Lippard to not use bareword filehandles.
# Modified 1 July 2026 by Jim Lippard after Claude Opus 4.8 review to
#    fix minor issues and make error checking more robust.
# Modified 15 October 2026 by Claude Opus 5.5 at the direction of Jim
#    Lippard to show a package the way OpenBSD's pkg_info does with no
#    options (setopts('cdMR') in OpenBSD::PkgInfo, unchanged in 7.9 and
#    8.0): "Required by:" from +REQUIRED_BY, sorted, between the comment
#    and the description, and "Install notice:" from +DISPLAY after the
#    description, each only if the file exists.

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

    opendir (my $dir_fh, $PKG_DIR) || die "Cannot open $PKG_DIR for reading file list. $!\n";
    @all_packages = grep { !/^\.{1,2}$/ && -d "$PKG_DIR/$_" } readdir ($dir_fh);
    closedir ($dir_fh);

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

    opendir (my $dir_fh, $PKG_DIR) || die "Cannot open $PKG_DIR for reading file list. $!\n";
    @all_packages = grep (!/^\.{1,2}$/, readdir ($dir_fh));
    closedir ($dir_fh);

    foreach $package (sort @all_packages) {
	next unless (-d "$PKG_DIR/$package");
	$package_name = '';
	my $pkg_fh;
	if (!open ($pkg_fh, '<', "$PKG_DIR/$package/+CONTENTS")) {
	    warn "Skipping $package: Cannot open +CONTENTS. $!\n";
	    next;
	}
	while (<$pkg_fh>) {
	    if (/^\@name (.*)$/) {
		$package_name = $1;
	    }
	}
	close ($pkg_fh);
	die "Cannot find \"\@name\" in +CONTENTS for package $package.\n" unless (defined ($package_name) && length ($package_name) > 0);

	my $desc_fh;
	if (!open ($desc_fh, '<', "$PKG_DIR/$package/+DESC")) {
	    warn "Skipping $package: Cannot open +DESC. $!\n";
	    next;
	}
	$one_liner = <$desc_fh>;
	$one_liner = '' unless defined ($one_liner);
	chomp ($one_liner);
	close ($desc_fh);

	printf "%-19s %s\n", $package_name, $one_liner;
    }
}

# Same sections, order and spacing as OpenBSD's pkg_info <pkg>: a header,
# then each section's banner, its lines and a blank line, then a blank
# line to end the package.
sub show_package_desc {
    my ($package) = @_;
    my ($one_liner);
    my $dir = "$PKG_DIR/$package";

    unless (-d $dir) {
        warn "Skipping $package: not a package directory.\n";
        return;
    }
    open (my $fh, '<', "$dir/+DESC") || die "Cannot open +DESC for package $package. $!\n";
    $one_liner = <$fh>;
    $one_liner = '' unless defined ($one_liner);
    chomp ($one_liner);
    print "Information for inst:$package\n\n";
    print "Comment:\n$one_liner\n\n";

    # Packages that depend on this one (written by pkg_add on OpenBSD).
    if (-f "$dir/+REQUIRED_BY") {
	print "Required by:\n";
	print_file ("$dir/+REQUIRED_BY", 1);
    }

    print "Description:\n";
    while (<$fh>) {
	chomp;
	print "$_\n";
    }
    close ($fh);
    print "\n";

    if (-f "$dir/+DISPLAY") {
	print "Install notice:\n";
	print_file ("$dir/+DISPLAY", 0);
    }

    # End of this package.
    print "\n";
}

# Print a registration file's lines (sorted if asked), then a blank line.
# Like pkg_info, a file that cannot be opened prints nothing at all.
sub print_file {
    my ($path, $sorted) = @_;

    open (my $fh, '<', $path) || return;
    my @lines = <$fh>;
    close ($fh);
    @lines = sort (@lines) if ($sorted);
    foreach my $line (@lines) {
	chomp ($line);
	print "$line\n";
    }
    print "\n";
}
