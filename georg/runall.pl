#!/usr/bin/perl -w
use Cwd;
use strict;
use warnings;

my $georgpath = "~/Research/fault-localization/georg";

my @dirs = @ARGV;
my $cwd = cwd();

for my $dir (@dirs) {
    chdir $cwd;
    chdir $dir;
    my @subdirs = glob "*";
    for my $subdir (@subdirs) {
	chdir $cwd;
	chdir $dir;
	chdir $subdir;
	my @files = glob "trace*.c";
	for my $file (@files) {
	    print "\n\n*** $dir $subdir $file ***\n";
	    system("time \$VERMEER_PATH/cil-1.7.3/bin/cilly -c --dodsnsmt --runsmtanalysistype=linearsearch $file");
	    `$georgpath/remap_variables $file smtresult.txt >$file.smtresult`;
	}
	`rm -r smt *.o smtresult.txt`;
    }
}
