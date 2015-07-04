#!/bin/bash

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

# Generate a bunch of tests
echo -ne "(*) Collecting test data ... 1 / 8"
"./$FILE.x" > header
head -n 1 < header > final_tests
tail -n +2 < header > tests
for i in `seq 2 8`; do
  echo -ne "\r(*) Collecting test data ... $i / 8"
  "./$FILE.x" | tail -n +2 >> tests
done

# Uniquify the tests and select at most 1024
sort -u tests | shuf -n 1536 >> final_tests

# Clean up
rm -rf header tests

# Call the monster
cd "$ROOT"
echo -ne "\n\n(*) Checking loop invariant:\n"
bin/clang++ --std=c++11 -c -w -Xclang -analyze                          \
            -Xclang -analyzer-checker=alpha.core.LoopInvariantChecker   \
            "$1"
