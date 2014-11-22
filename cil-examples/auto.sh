#!/bin/sh

if [ $# -ne 1 ]; then
    echo "Needs an argument."; exit 1
fi

echo "[[ RUNLINEAR ]]"
./runlinear $1
EXIT=$?
cd $1_dir; rm -f a.out *.i *.o; cd ..
if [ "$EXIT" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNCONCRETE ]]"
./runconcrete $1
EXIT=$?
cd $1_dir; rm -f a.out *.i *.o; cd ..
if [ "$EXIT" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNRMTMPS ]]"
./runrmtmps $1
cd $1_dir; rm -f *.i *.o; cd ..
if [ "$?" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNSSA ]]"
./runssa $1
cd $1_dir; rm -f *.i *.o; cd ..
if [ "$?" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNSNAPS ]]"
./runsnaps $1
cd $1_dir; rm -f a.out *.i *.o; cd ..
if [ "$?" -ne "0" ]; then exit 1; fi

echo
echo "[[ COMPILATION ]]"
gcc $1_dir/$1.ssa.snaps.c
rm -f a.out
if [ "$?" -eq "0" ]; then echo "OK"; else echo "ERROR"; fi
