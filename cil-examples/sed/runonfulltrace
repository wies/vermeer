#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly -c --dodsnssa --save-temps "$1.postconcrete.c" -lm
mv "$1.postconcrete.cil.c" "$1.ssa.c"
../../../cil-1.7.3/bin/cilly -c --dodsnsmt  "$1.ssa.c"
../../remap_variables "$1.ssa.c" smtresult.txt > remapped.txt
