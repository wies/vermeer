#!/bin/bash
if [ "$#" -ne 2 ] 
then echo "needs two args";
    exit 1
fi

../bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --save-temps $1
./a.out > $2
