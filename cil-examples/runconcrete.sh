#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

CIL_TMP_DIR="$1_dir"
if [ ! -e $CIL_TMP_DIR ]; then
    echo "$CIL_TMP_DIR is missing";
    exit 1
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnconcrete --save-temps=$CIL_TMP_DIR "$CIL_TMP_DIR/$1.postlinear.c" dsnlog.o extern_debug_funs.o -lm

if [ "$?" -ne "0" -o ! -x ./a.out ]; then exit 1; fi
./a.out
mv dsn_logfile.txt "$CIL_TMP_DIR/$1.concrete.c"

./postprocess_concrete "$CIL_TMP_DIR/$1.concrete.c" > "$CIL_TMP_DIR/$1.postconcrete.c"
