#!/bin/bash

echo -n "" > log.txt
for ex in ./*.smt2
do
  runEx=$(aeval $ex)
  runResult="$runEx"
  if [[ "$runResult" == *"0" ]]
  then
    echo "$ex failed, following are the detail:" >> log.txt
    echo "$runResult" | grep . >> log.txt
  else
    echo "$ex returned 1, success!" >> log.txt
  fi
  echo >> log.txt
done
