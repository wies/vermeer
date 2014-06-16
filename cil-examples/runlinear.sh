#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsn --save-temps "$1.c" -lm
./a.out > "$1.linear.c"
