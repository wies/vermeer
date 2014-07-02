#!/bin/bash

if [ -z $1 ]; then
    echo "Source file not provided."; exit 1
fi

SRC=$1
SUFFIX=`echo $1 | sed -e 's/.*\.\([^.]*\)/\1/'`
NO_SUFFIX=`echo $1 | sed -e 's/\(.*\)\.[^.]*/\1/'`
shift

echo "File: $SRC"
echo "Without suffix: $NO_SUFFIX"
echo "Suffix: $SUFFIX"

set -o xtrace

# Preprocess the source code with gcc.
gcc -E -P $* $SRC > $SRC.tmp_in

# Parse, construct AST, instrument, and output manipulated code.
java -cp ../../code/parser:../../code/parser/xtc.jar Tenderizer $SRC.tmp_in > $SRC.tmp_out

# We are almost done. Strip out the first two lines (tool information).
LINES=`wc -l $SRC.tmp_out | awk '{print $1}'`
let LINES=LINES-2
tail -$LINES $SRC.tmp_out > $NO_SUFFIX.tendered.$SUFFIX

set +o xtrace
