#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnlinear --no-convert-direct-calls --save-temps "$1.c" ../../dsnlog.o -lm

./a.out sample.cnf
mv dsn_logfile.txt "$1.linear.c"

../../postprocess_linear "$1.linear.c" > "$1.postlinear.c"
