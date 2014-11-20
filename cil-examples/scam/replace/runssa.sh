#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly -c --dodsnssa --useLogicalOperators --save-temps "$1.postconcrete.notmps.c"
mv "$1.postconcrete.notmps.cil.c" "$1.ssa.c"
