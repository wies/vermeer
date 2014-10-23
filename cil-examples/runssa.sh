#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly --dodsnssa --save-temps "$1.postconcrete.c" -lm
mv "$1.postconcrete.cil.c" "$1.ssa.c"
