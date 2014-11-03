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

../cil-1.7.3/bin/cilly -c --dodsnsmt  "$CIL_TMP_DIR/$1.ssa.c" -lm
