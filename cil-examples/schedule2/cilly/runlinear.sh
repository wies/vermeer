#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --no-convert-direct-calls --dodsnlinear --save-temps "$1.c" ../../dsnlog.o -lm
#this comes from runall.sh test 2476
./a.out 2 7 9 < ft.6 > output.txt
mv dsn_logfile.txt "$1.linear.c"

../../postprocess_linear "$1.linear.c" > "$1.postlinear.c"
