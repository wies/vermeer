#!/bin/bash
TRACE="trace_assertion_failed_139.c"
ARGS="--smtmultithread=allthreads --flowsensitive --hazardsensitivewar --nointrathreadhazard" 

time $VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --smtcalcstats $ARGS $TRACE

python ../scripted-experiments/beautify_explanation.py reduced.txt > reduced.beautify.txt;
python ../scripted-experiments/beautify_explanation.py threadSlice0.txt > threadSlice0.beautify.txt;
python ../scripted-experiments/beautify_explanation.py threadSlice1.txt > threadSlice1.beautify.txt;
python ../scripted-experiments/beautify_explanation.py threadSlice2.txt > threadSlice2.beautify.txt;


../remap_variables $TRACE reduced.beautify.txt > reduced.remap.txt;
../remap_variables $TRACE threadSlice0.beautify.txt > threadSlice0.remap.txt;
../remap_variables $TRACE threadSlice1.beautify.txt > threadSlice1.remap.txt;
../remap_variables $TRACE threadSlice2.beautify.txt > threadSlice2.remap.txt;


