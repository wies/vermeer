#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

if [ ! -f dsnlog.o ]; then
    . mk-log-o
fi

CIL_TMP_DIR="$1_dir"

if [ ! -e $CIL_TMP_DIR ]; then
    mkdir $CIL_TMP_DIR
fi

../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnlinear --save-temps=$CIL_TMP_DIR "$1.c" dsnlog.o extern_debug_funs.o -lm

if [ "$?" -ne "0" -o ! -x ./a.out ]; then exit 1; fi
./a.out 
mv dsn_logfile.txt "$CIL_TMP_DIR/$1.linear.c"

./postprocess_linear "$CIL_TMP_DIR/$1.linear.c" > "$CIL_TMP_DIR/$1.postlinear.c"
