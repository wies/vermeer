#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

$VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --runsmtanalysistype=binarysearch --smtmultithread=abstractenv "$1.c" -lm
$VERMEER_PATH/georg/remap_variables "$1.c" smtresult.txt > "$1.result.txt"
rm smtresult.txt
rm *.o

