#!/bin/bash
TRACE="trace_assertion_failed_5.c"
ARGS="--smtmultithread=allthreads --flowsensitive --hazardsensitiveall --nointrathreadhazard --runsmtanalysistype=binarysearch " 
BEAUTIFY="python $VERMEER_PATH/georg/scripted-experiments/beautify_explanation.py"
REMAP="$VERMEER_PATH/georg/remap_variables"
time $VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --smtcalcstats $ARGS $TRACE | tee out.txt

$BEAUTIFY reduced.txt > reduced.beautify.txt;
$BEAUTIFY threadSlice0.txt > threadSlice0.beautify.txt;
$BEAUTIFY threadSlice1.txt > threadSlice1.beautify.txt;
$BEAUTIFY threadSlice2.txt > threadSlice2.beautify.txt;

$REMAP $TRACE reduced.beautify.txt > reduced.remap.txt;
$REMAP $TRACE threadSlice0.beautify.txt > threadSlice0.remap.txt;
$REMAP $TRACE threadSlice1.beautify.txt > threadSlice1.remap.txt;
$REMAP $TRACE threadSlice2.beautify.txt > threadSlice2.remap.txt;

