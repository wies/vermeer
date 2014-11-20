#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --useLogicalOperators --save-temps "$1.postlinear.c" ../../dsnlog.o

if [ "$?" -ne "0" -o ! -x ./a.out ]; then exit 1; fi
./a.out '--*[@t]-' 'b@t' < 174.inp.78.1
mv dsn_logfile.txt "$1.concrete.c"

../../postprocess_concrete "$1.concrete.c" > "$1.postconcrete.c"
