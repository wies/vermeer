#!/bin/bash
if [ "$#" -ne 2 ] 
then echo "needs two args";
    exit 1
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --save-temps $1
./a.out > $2
