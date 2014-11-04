#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnlinear --save-temps "$1.c" ../../dsnlog.o -lm -I. -DFAULTY_F_DG_4
./a.out '-G' '[H]' file000583
mv dsn_logfile.txt "$1.linear.c"

../../postprocess_linear "$1.linear.c" > "$1.postlinear.c"
