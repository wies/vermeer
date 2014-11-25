#!/bin/sh

# Format: list of "<directory>:<prog name>".
EXAMPLES="simple:simple  sed:sed  tcas:tcas  replace:replace  schedule2:schedule2  gzip:allfile  grep:grep  MiniSat-C_v1.14.1:solver"

DIFF_REPORT=`pwd`/diff_report.txt


if [ ! -x "$VERMEER_PATH/bin/runexplain" ]; then
    echo "[TEST] Cannot run runexplain; check \$VERMEER_PATH."; exit 1
fi

rm -f $DIFF_REPORT

for DIR_AND_PROG in $EXAMPLES; do
    DIR=`echo $DIR_AND_PROG | cut -d':' -f 1`
    PROG=`echo $DIR_AND_PROG | cut -d':' -f 2`

    cd $VERMEER_PATH/examples/$DIR
    rm -rf ${PROG}_dir

    runlinear $PROG
    runconcrete $PROG

    if [ -e "README" ]; then
        ASSERT=`grep 'assert(.*);' README`
        if [ ! -z "$ASSERT" ]; then
            sed -e "s/.*\/\/ Looks like the concretized trace ran into a crash.*/$ASSERT\n\0/" \
                ${PROG}_dir/$PROG.postconcrete.c > tmp
            mv -f tmp ${PROG}_dir/$PROG.postconcrete.c
        fi
    fi

    runrmtmps $PROG
    runssa $PROG

    for ALGO in unsatcore noninductive binarysearch; do
        runsmt $PROG $ALGO

        SRC=${PROG}_dir/explanation.txt
        TRGT=$VERMEER_PATH/tests/output.$PROG.$ALGO.txt
        if [ "$1" = "snapshot" ]; then
            OVERWRITE=Y
            if [ -e "$TRGT" ]; then
                echo "[TEST] \"$TRGT\" exists."
                echo "[TEST] Overwrite (y/[n])? "
                read OVERWRITE
            fi
            if [ "$OVERWRITE" = "Y" -o "$OVERWRITE" = "y" ]; then
                cp -f $SRC $VERMEER_PATH/tests/output.$PROG.$ALGO.txt
            fi
        else
            if [ ! -e "$TRGT" ]; then
                echo "[TEST] \"$TRGT\" does not exist; take a snapshot first:"
                echo "[TEST]    $ $0 snapshot"
                exit 1
            fi
            diff -u $SRC $TRGT >> $DIFF_REPORT
        fi
    done
done

echo
echo "Check $DIFF_REPORT for any changes."
