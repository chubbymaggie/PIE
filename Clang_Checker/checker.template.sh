#!/bin/bash

MAX_RUNS=128
MAX_TESTS=4096

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

FILE="`basename \"$1\"`"
WORKING_PATH="__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__/$FILE"

# Compile the program
cd "`dirname \"$1\"`"
g++ --std=c++11 "$FILE" -o "$FILE.x"

rm -rf "$WORKING_PATH"
mkdir "$WORKING_PATH"
cp "$FILE" "$WORKING_PATH/"
mv "$FILE.x" "$WORKING_PATH/"
cd "$WORKING_PATH"

# Generate a bunch of tests from $MAX_RUNS successful runs
"./$FILE.x" > header
head -n 1 < header > final_tests
echo "" > tests
for i in `seq 1 $MAX_RUNS`; do
  echo -ne "\r(*) Collecting test data ... $i / $MAX_RUNS"
  TESTS=`"./$FILE.x"`
  while [ $? -ne 0 ]; do
    TESTS=`"./$FILE.x"`
  done
  echo "$TESTS" | tail -n +2 >> tests
done

# Uniquify the tests and select at most $MAX_TESTS
sort -u tests | shuf -n $MAX_TESTS >> final_tests
TESTS="`wc -l final_tests`"
echo " ==> $TESTS."

# Clean up
rm -rf header tests

# Call the monster
cd "$ROOT"
echo -ne "\n(*) Checking loop invariant:\n"
bin/clang++ --std=c++11 -c -w -Xclang -analyze                          \
            -Xclang -analyzer-checker=alpha.core.LoopInvariantChecker   \
            "$1"
