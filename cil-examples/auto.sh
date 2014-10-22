#!/bin/sh

if [ $# -ne 1 ]; then
    echo "Needs an argument."; exit 1
fi

echo "[[ RUNLINEAR ]]"
./runlinear.sh $1
EXIT=$?
rm -f a.out $1.o $1.i $1.cil.i
if [ "$EXIT" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNCONCRETE ]]"
./runconcrete.sh $1
EXIT=$?
rm -f ./a.out $1.postlinear.o $1.postlinear.i $1.postlinear.cil.i
if [ "$EXIT" -ne "0" ]; then exit 1; fi
