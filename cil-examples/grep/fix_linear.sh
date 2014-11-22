#!/bin/sh

grep -v ':alpha:' "grep.postlinear.c"            \
  | grep -hv '^static struct .* prednames\[13\]' \
  | sed -e 's/, & [EFG]compile/, 12345/g'        \
        -e 's/, & \(EG\|F\)execute/, 54321/g'    > tmp
mv -f tmp "grep.postlinear.c"
