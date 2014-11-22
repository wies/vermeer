#!/bin/sh

mv -f sed.postlinear.c tmp
../fix_decls tmp > sed.postlinear.c
rm -f tmp
