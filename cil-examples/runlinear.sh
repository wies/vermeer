#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnlinear --save-temps "$1.c" dsnlog.o -lm

if [ "$?" -ne "0" -o ! -x ./a.out ]; then exit 1; fi
./a.out 
mv dsn_logfile.txt "$1.linear.c"
