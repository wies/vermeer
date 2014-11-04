#!/usr/bin/perl

#please change KLEE_PATH to where you put our version of KLEE
$KLEE_PATH = "/home/wei/Documents/code/klee2.7/klee/Release/bin/";


#-- Following is an example of applying our system on a bug in mkdir utility.
#-- This bug is found in KLEE paper, and we use this bug to demonstrate how
#-- to run our system here.

#-- Execute mkdir program with failure input and collect field information
#-- (call sequence) by using option (--use-concrete-call)

$record = `$KLEE_PATH/klee --optimize --libc=uclibc --posix-runtime --init-env --use-concrete-call ./grep.bc -G \'[\\]\' A`;
print "$record";

#-- Two files will be generated after the execution callseq(recorded call sequence)
#-- and funcov(Coverage information in terms of function level).

#-- Now we use replay call sequence option to try to generate new input to trigger this bug.
#-- Notice that we are using symbolic inputs to the program.

$replay = `$KLEE_PATH/klee --optimize --libc=uclibc --posix-runtime --init-env --use-call-seq-replay ./grep.bc --sym-arg 2 --sym-arg 3 A --sym-files 1 10`;

open(REPLAYFILE,'>replayoutput');
print REPLAYFILE "$replay";
close(REPLAYFILE);

