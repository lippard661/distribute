distribute.pl and install.pl perl scripts to distribute files to multiple hosts and install them.
install.pl includes minimal functionality to support installing OpenBSD packages (for portable stuff like perl) on non-OpenBSD systems,
similar to OpenBSD's pkg_add and pkg_delete.
pkg_info.pl is a minimal implementation of OpenBSD's pkg_info to go along with that.

Current version of distribute.pl from 3 January 2026.
Current version of distribute.conf from 14 September 2025.
Current version of install.pl from 3 January 2026.
Current version of pkg_info.pl from 5 October 2025.

Intended primarily for OpenBSD hosts that use immutable file systems, but also works on Linux, I use it with Proxmox (Debian), Kali Linux, and macOS.
install.pl will install perl modules into an appropriate location for Linux (at least Debian and Kali) and
macOS, and rewrite the /var/db/pkg +CONTENTS file to match.  At some point I may split out the minimal package manager
stuff from install.pl into a separate module and provide a separate pkg_add.pl and pkg_delete.pl.

Also uses Signify.pm and syslock/sysunlock; I use it with rrsync (in my rsync-tools repo).
Signify.pm now supports Linux when used with the signify-openbsd apt package and macOS when used with signify-osx (Homebrew).

Also available at https://www.discord.org/lippard/software/
