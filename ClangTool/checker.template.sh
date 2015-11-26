#!/bin/bash

MAX_RUNS=256

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

SOURCE_FILE="$1"
MAX_TESTS="$2"
USE_TOOL="$3"
CGROUP="$4"
CONFLICT_SIZE="$5"

if [[ ! -f "$SOURCE_FILE" ]]; then
  echo "--- File $SOURCE_FILE doesn't exist. ABORT ---"
  exit 1
fi

if [[ "$USE_TOOL" == "" ]]; then
    USE_TOOL="pie"
fi

FILE="`basename \"$SOURCE_FILE\"`"
CG_LOCATION="/sys/fs/cgroup/memory/$CGROUP"
ABDUCER_PATH="__ABDUCER_PATH_FROM_SETUP_SCRIPT__"

if [[ "$CONFLICT_SIZE" == "" || "$USE_TOOL" != "pie" ]]; then
    CONFLICT_SIZE="all"
fi

if [[ "$CGROUP" != "" ]]; then
    WORKING_PATH="__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__/$CGROUP/$MAX_TESTS/$USE_TOOL/$CONFLICT_SIZE/$FILE"
else
    WORKING_PATH="__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__/$MAX_TESTS/$USE_TOOL/$CONFLICT_SIZE/$FILE"
fi

TOTAL_LOG="$WORKING_PATH/TOTAL.LOG"
aterrcho() { echo "$@" | tee -a "$TOTAL_LOG" 1>&2 ; }
aterrcat() { cat "$@" | tee -a "$TOTAL_LOG" 1>&2 ; }

# Compile the program
cd "`dirname \"$SOURCE_FILE\"`"
g++ --std=c++11 "$FILE" -o "$FILE.x" 2>&1

if [[ $? -ne 0 ]]; then
  exit 1
fi

rm -rf "$WORKING_PATH"
mkdir -p "$WORKING_PATH"
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
aterrcho " ==> $TESTS."

# Clean up & link
rm -rf header tests
"$ABDUCER_PATH/link.sh" "$WORKING_PATH"

# Call the monster
cd "$ROOT"
aterrcho -ne "\n(*) Checking loop invariant:\n"

EXEC_CMD="time bin/pinvgen -wpath $WORKING_PATH -abducer $ABDUCER_PATH/abduce.sh    \
                           -tool=$USE_TOOL -csize $CONFLICT_SIZE --extra-arg=--std=c++11 $SOURCE_FILE --"
echo "$EXEC_CMD" > checker_exec.sh

if [[ "$CGROUP" != "" ]]; then
    echo 0 > "$CG_LOCATION/memory.force_empty"
    echo 0 > "$CG_LOCATION/memory.memsw.failcnt"
    echo 0 > "$CG_LOCATION/memory.memsw.max_usage_in_bytes"
    cgexec -g memory,cpu:$CGROUP bash checker_exec.sh 2>&1 | tee -a "$TOTAL_LOG"
else
    bash checker_exec.sh 2>&1 | tee -a "$TOTAL_LOG"
fi
rm checker_exec.sh

COUNTER_PREFIX="count"
aterrcho -ne "\n\n--- Processed $FILE ---\n"
for EXT in "sat" "unsat" "unk" "escher"; do
  aterrcho -n "$EXT: "
  COUNTER_FILE="$WORKING_PATH/$COUNTER_PREFIX.$EXT"
  [[ -f "$COUNTER_FILE" ]] && aterrcat "$COUNTER_FILE" || aterrcho "0"
done

if [[ "$CGROUP" != "" ]]; then
    aterrcho -ne "\n[$] OOM Count = " ; aterrcat "$CG_LOCATION/memory.memsw.failcnt"
    aterrcho -ne "[$] MAX Usage = " ; aterrcho $(( $(cat "$CG_LOCATION/memory.memsw.max_usage_in_bytes") / ( 1024 * 1024 ) ))
fi

sed -i s//\\\n/g "$TOTAL_LOG"
