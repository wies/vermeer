#!/bin/sh

if [ $# -ne 1 ]; then
    echo "Needs an argument."; exit 1
fi

echo "[[ RUNLINEAR ]]"
./runlinear.sh $1
EXIT=$?
cd $1_dir; rm -f a.out $1.o $1.i $1.cil.i; cd ..
if [ "$EXIT" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNCONCRETE ]]"
./runconcrete.sh $1
EXIT=$?
cd $1_dir; rm -f a.out $1.postlinear.o $1.postlinear.i $1.postlinear.cil.i; cd ..
if [ "$EXIT" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNRMTMPS ]]"
./runrmtmps.sh $1
cd $1_dir; rm -f $1.postconcrete.o $1.postconcrete.i $1.postconcrete.cil.i; cd ..
if [ "$?" -ne "0" ]; then exit 1; fi

echo
echo "[[ COMPILATION ]]"
gcc $1_dir/$1.postconcrete.notmps.c
rm -f a.out
if [ "$?" -eq "0" ]; then echo "OK"; else echo "ERROR"; fi
