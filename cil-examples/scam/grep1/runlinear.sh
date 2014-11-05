#!/bin/bash
if [ "$#" -ne 1 ] 
then echo "needs an argument";
    exit 1
fi

../../../cil-1.7.3/bin/cilly --dosimpleMem --dosimplify --domakeCFG --dodsnlinear --no-convert-direct-calls --save-temps "$1.c" ../../dsnlog.o -lm -I. -DCO_FIX -DFAULTY_F_DG_4

./a.out '-G' '[H]' file000583
mv dsn_logfile.txt "$1.linear.c"

../../postprocess_linear "$1.linear.c" > "$1.postlinear.broken.c"

# Manual editing after postprocess_linear.
grep -v ':alpha:' "$1.postlinear.broken.c"                                    \
  | grep -hv '^static struct .* prednames\[13\]'                              \
  | sed -e 's/, & [EFG]compile/, 12345/g'                                     \
        -e 's/, & \(EG\|F\)execute/, 54321/g'                                    \
  > "$1.postlinear.c"
