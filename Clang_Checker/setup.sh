#!/bin/bash

CLANG_ROOT="$1"

OWN_ROOT="`dirname "$0"`"
OWN_ROOT="`cd $OWN_ROOT && pwd`"

MISTRAL_ROOT="$2"
ABDUCER_ROOT="$3"

cd "$CLANG_ROOT/lib/StaticAnalyzer/Checkers/"
patch -bN < "$OWN_ROOT/patch"

perl -pe 's#__MISTRAL_PATH_FROM_SETUP_SCRIPT__#"'"$MISTRAL_ROOT"'"#g' < "$OWN_ROOT/LoopInvariantChecker.template.cpp" > LoopInvariantChecker.cpp
perl -pi -e 's#__ABDUCER_PATH_FROM_SETUP_SCRIPT__#"'"$ABDUCER_ROOT"'"#g' LoopInvariantChecker.cpp
