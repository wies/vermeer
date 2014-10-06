#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --save-temps "$1.linear.c" dsnlog.o -lm
./a.out
mv dsn_logfile.txt "$1.concrete.c"
