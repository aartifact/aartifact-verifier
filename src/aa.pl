################################################################
##
## aartifact
## http://www.aartifact.org/
##
## src/aa.pl
##
##   Perl wrapper script that can be useful if ANSI color codes
##   are not displayed properly by the console or environment.
##

################################################################
##

#!/usr/bin/perl
use strict;
use warnings;

my $args = "";
foreach my $i (0 .. $#ARGV) {$args .= "$ARGV[$i] ";}
my @o = qx(aa $args);
foreach my $l (@o) { print $l; }

#eof