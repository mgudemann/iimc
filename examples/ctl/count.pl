#! /usr/bin/perl -w

# Count number of passing and failing formulae in CTL files.
#
# Usage: ./count.pl
#
# This counts all the properties in .ctl files in the current directory.
# Additional files can be passed on the command line.
# It relies on #PASS: and #FAIL: tags.  It does minimal checks.

use strict;

#Add all .ctl files in current directory and then remove duplicates.
push(@ARGV, glob("*.ctl"));
my %seen;
@ARGV = grep !$seen{$_}++, @ARGV;

my $countPass = 0;
my $countFail = 0;
while (<>) {
    chop;
    if (/#PASS:\s*\((\d+)\)/) {
        $countPass++;
    } elsif (/#PASS:\s*\((\d+)-(\d+)\)/) {
        my $ub = $2;
        my $lb = $1;
        die "Incorrect range: $_\n" unless $ub > $lb;
        $countPass += $ub - $lb + 1;
    } elsif (/#FAIL:\s*\((\d+)\)/) {
        $countFail++;
    } elsif (/#FAIL:\s*\((\d+)-(\d+)\)/) {
        my $ub = $2;
        my $lb = $1;
        die "Incorrect range: $_\n" unless $ub > $lb;
        $countFail += $ub - $lb + 1;
    } elsif (/#FAIL:/ or /#PASS:/) {
        die "Missing index: $_\n";
    }
}
print "Number of passing properties = " . $countPass . "\n";
print "Number of failing properties = " . $countFail . "\n";
print "Total number of properties   = " . ($countPass + $countFail) . "\n";

exit 0;
