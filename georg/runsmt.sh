#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

$VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --smtmultithread "$1.c" -lm
$VERMEER_PATH/georg/remap_variables "$1.c" smtresult.txt > "$1.result.txt"
rm smtresult.txt
rm *.o

$VERMEER_PATH/cil-1.7.3/bin/cilly -c --keepunused --dodsnsmt --smtmultithread  "$1.c" -lm
$VERMEER_PATH/georg/remap_variables "$1_unscoped.c" smtresult.txt > "$1_unscoped.result.txt"
rm smtresult.txt
rm *.o
