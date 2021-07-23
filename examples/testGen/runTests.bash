#!/bin/bash

echo -n "" > log.txt
for ex in ./*.smt2
do
  printf "Running: $ex\n"
  printf "$(gtimeout 5 aeval --skol --debug $ex)\n\n\n"
  # if [[ "$runResult" == *"0" ]]
  # then
  #   echo "$ex failed, following are the detail:" >> log.txt
  #   echo "$runResult" | grep . >> log.txt
  # else
  #   echo "$ex returned 1, success!" >> log.txt
  # fi
  printf "$runEx"
done
