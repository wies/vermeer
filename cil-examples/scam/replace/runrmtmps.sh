#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly -c --dodsnrmtmps --save-temps "$1.postconcrete.c"
mv "$1.postconcrete.cil.c" "$1.postconcrete.notmps.c"