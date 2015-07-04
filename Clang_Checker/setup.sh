#!/bin/bash

OWN_ROOT="`dirname "$0"`"
OWN_ROOT="`cd \"$OWN_ROOT\" && pwd`"

LLVM_ROOT="`cd \"$1\" && pwd`"
WORKING_ROOT="`cd \"$2\" && pwd`"

MISTRAL_ROOT="`cd ../mistral/ && pwd`"
ABDUCER_ROOT="`cd ../abducer/ && pwd`"

cd "$LLVM_ROOT/tools/clang/lib/StaticAnalyzer/Checkers/"
patch -bN < "$OWN_ROOT/patch"

perl -pe 's#__MISTRAL_PATH_FROM_SETUP_SCRIPT__#'"$MISTRAL_ROOT"'#g' < "$OWN_ROOT/LoopInvariantChecker.template.cpp" > LoopInvariantChecker.cpp
perl -pi -e 's#__ABDUCER_PATH_FROM_SETUP_SCRIPT__#'"$ABDUCER_ROOT"'#g' LoopInvariantChecker.cpp
perl -pi -e 's#__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__#'"$WORKING_ROOT"'#g' LoopInvariantChecker.cpp

cd "$LLVM_ROOT"
mkdir build ; cd build
cmake .. && make

perl -pe 's#__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__#'"$WORKING_ROOT"'#g' < "$OWN_ROOT/checker.template.sh" > checker
