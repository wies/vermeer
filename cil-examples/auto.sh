#!/bin/sh

if [ $# -ne 1 ]; then
    echo "Needs an argument."; exit 1
fi

echo "[[ RUNLINEAR ]]"
./runlinear.sh $1
EC=$?
rm -f a.out $1.o $1.i $1.cil.i
if [ "$EC" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNCONCRETE ]]"
./runconcrete.sh $1
EC=$?
rm -f ./a.out $1.postlinear.o $1.postlinear.i $1.postlinear.cil.i
if [ "$EC" -ne "0" ]; then exit 1; fi

echo
echo "[[ POSTPROCESS_CONCRETE ]]"
./postprocess_concrete $1.concrete.c > $1.concrete.c.tmp
EC=$?
if [ "$EC" -ne "0" ]; then rm -f $1.concrete.c.tmp; exit 1; fi
mv -f $1.concrete.c.tmp $1.concrete.c
cat $1.concrete.c
