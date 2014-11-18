#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --save-temps "$1.postlinear.c" ../../dsnlog.o -lm

if [ "$?" -ne "0" -o ! -x ./a.out ]; then exit 1; fi
#this comes from runall.sh test 2476
./a.out 2 7 9 < ft.6 > output.txt
mv dsn_logfile.txt "$1.concrete.c"

../../postprocess_concrete "$1.concrete.c" > "$1.postconcrete.c"
