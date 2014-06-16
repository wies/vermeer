#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --save-temps "$1.linear.c"  
./a.out > "$1.concrete.c"-lm
