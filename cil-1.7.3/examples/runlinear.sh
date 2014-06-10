#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsn --save-temps "$1.c"
./a.out > "$1.linear.c"
