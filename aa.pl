################################################################
##
## aartifact
## http://www.aartifact.org/src/
## Copyright (C) 2008-2011
## A. Lapets
##
## This software is made available under the GNU GPLv3.
##
## aa.pl
##   Perl wrapper script that can be useful if ANSI color codes
##   are not displayed properly by the console or environment.

################################################################
##

#!/usr/bin/perl
use strict;
use warnings;

my $args = "";
foreach my $i (0 .. $#ARGV) {$args .= "$ARGV[$i] ";}
my @o = qx(aa $args);
foreach my $l (@o) { print $l; }
