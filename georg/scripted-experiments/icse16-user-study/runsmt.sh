#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

$VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=allthreads --flowsensitive --toposortinput --hazardsensitiveall --nointrathreadhazard --smtbeautify "$1.c" -lm
rm -f *.o

