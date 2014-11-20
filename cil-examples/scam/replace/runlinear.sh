#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnlinear --useLogicalOperators --no-convert-direct-calls --save-temps "$1.c" ../../dsnlog.o

./a.out '--*[@t]-' 'b@t' < 174.inp.78.1
mv dsn_logfile.txt "$1.linear.c"

../../postprocess_linear "$1.linear.c" > "$1.postlinear.c"
