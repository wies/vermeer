#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --no-convert-direct-calls --dodsnlinear --save-temps "$1.c" ../../dsnlog.o -lm
./a.out -f pattern000001 file000001
mv dsn_logfile.txt "$1.linear.c"

../../postprocess_linear "$1.linear.c" > "tmp"
./fix_decls "tmp" > "$1.postlinear.c"
rm tmp