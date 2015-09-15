#!/bin/bash

MAX_RUNS=240
MAX_TESTS=6400

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

if [[ ! -f "$1" ]]; then
  echo "--- File $1 doesn't exist. ABORT ---"
  exit 1
fi

FILE="`basename \"$1\"`"
ABDUCER_PATH="__ABDUCER_PATH_FROM_SETUP_SCRIPT__"
WORKING_PATH="__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__/$FILE"

# Compile the program
cd "`dirname \"$1\"`"
g++ --std=c++11 "$FILE" -o "$FILE.x" 2>&1

if [[ $? -ne 0 ]]; then
  exit 1
fi

rm -rf "$WORKING_PATH"
mkdir "$WORKING_PATH"
ln -rfs "$FILE" "$WORKING_PATH/$FILE"
mv "$FILE.x" "$WORKING_PATH/"

# Generate a bunch of tests from $MAX_RUNS successful runs
cd "$WORKING_PATH"
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

# Clean up & link
rm -rf header tests
"$ABDUCER_PATH/link.sh" "$WORKING_PATH"

# Call the monster
cd "$ROOT"
echo -ne "\n(*) Checking loop invariant:\n"
bin/pinvgen --extra-arg=--std=c++11 "$1" --
