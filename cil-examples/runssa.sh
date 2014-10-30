#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly -c --dodsnssa --save-temps "$1.sll.c" -lm
mv "$1.sll.cil.c" "$1.ssa.c"
