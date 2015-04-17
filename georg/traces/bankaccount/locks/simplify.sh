#!/bin/bash
TRACE="trace_assertion_failed_5.c"
ARGS="--smtmultithread=allthreads --flowsensitive  --nointrathreadhazard --runsmtanalysistype=binarysearch " 
BEAUTIFY="python $VERMEER_PATH/georg/scripted-experiments/beautify_explanation.py"
REMAP="$VERMEER_PATH/georg/remap_variables"
time $VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --smtcalcstats --smtbeautify $ARGS $TRACE | tee out.txt


$REMAP $TRACE reduced.txt > reduced.remap.txt;
$REMAP $TRACE threadSlice0.txt > threadSlice0.remap.txt;
$REMAP $TRACE threadSlice1.txt > threadSlice1.remap.txt;
$REMAP $TRACE threadSlice2.txt > threadSlice2.remap.txt;

