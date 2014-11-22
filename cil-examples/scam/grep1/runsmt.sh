#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly -c --dodsnsmt --runsmtanalysistype=binarysearch --smtdebug "$1.ssa.c"
../../remap_variables "$1.ssa.c" smtresult.txt > remapped.txt
