#!/bin/bash

compile=$(g++ testGenerator.cpp -std=c++11 -o testGen)
$compile
rm genEx*.smt2
testGen=$(./testGen)
declare -i fileCt=$1
declare -i cur=1
while [ $cur -le $fileCt ]
do
   echo "$(./testGen)" >> "genEx$cur.smt2"
   cur=$cur+1
done
