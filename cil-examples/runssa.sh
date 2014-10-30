#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly -c --dodsnssa --save-temps "$1.postconcrete" -lm
mv "$1.postconcrete" "$1.ssa.c"
