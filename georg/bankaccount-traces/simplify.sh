#!/bin/bash
time $VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --smtcalcstats --runsmtanalysistype=binarysearch --smtmultithread=allthreads --flowsensitive --hazardsensitivewar --nointrathreadhazard trace_assertion_failed_139.c

python ../scripted-experiments/beautify_explanation.py threadSlice0.txt >out0.txt;
python ../scripted-experiments/beautify_explanation.py threadSlice1.txt >out1.txt;
python ../scripted-experiments/beautify_explanation.py threadSlice2.txt >out2.txt;

../remap_variables trace_assertion_failed_139.c out0.txt > remap0.txt
../remap_variables trace_assertion_failed_139.c out1.txt > remap1.txt
../remap_variables trace_assertion_failed_139.c out2.txt > remap2.txt
