#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../cil-1.7.3/bin/cilly -c --dodsnsmt  "$1.c" -lm
../remap_variables "$1.c" smtresult.txt > "$1.result.txt"
rm smtresult.txt
rm *.o

../../cil-1.7.3/bin/cilly -c --dodsnsmt  "$1.c" -lm
../remap_variables "$1_unscoped.c" smtresult.txt > "$1_unscoped.result.txt"
rm smtresult.txt
rm *.o
