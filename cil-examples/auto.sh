#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Needs an argument."; exit 1
fi

echo "[[ RUNLINEAR ]]"
./runlinear.sh $1
EC=$?
rm -f a.out $1.o $1.i $1.cil.i
if [ "$EC" -ne "0" ]; then exit 1; fi

echo
echo "[[ POSTPROCESS_LINEAR ]]"
./postprocess_linear $1.linear.c > $1.post.tmp
if [ "$?" -ne "0" ]; then rm -f $1.post.tmp; exit 1; fi

sed -e 's/^  __return__1 = /  int __return__1 = /' $1.post.tmp > $1.post.tmp2
LINES=`wc $1.post.tmp2 | awk '{print $1}'`
let LINES-=1
tail -$LINES $1.post.tmp2 > $1.post.linear.c
rm -f $1.post.tmp $1.post.tmp2

echo
echo "[[ RUNCONCRETE ]]"
./runconcrete.sh $1.post
EC=$?
rm -f ./a.out $1.post.linear.o $1.post.linear.i $1.post.linear.cil.i
if [ "$EC" -ne "0" ]; then exit 1; fi

echo
echo "[[ RUNCONCRETE_CONCRETE ]]"
./postprocess_concrete $1.post.concrete.c
