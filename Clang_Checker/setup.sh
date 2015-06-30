#!/bin/bash

CLANG_ROOT="$1"

OWN_ROOT="`dirname "$0"`"
OWN_ROOT="`cd $OWN_ROOT && pwd`"

cd "$CLANG_ROOT/lib/StaticAnalyzer/Checkers/"
patch -b < "$OWN_ROOT/patch"
cp "$OWN_ROOT/LoopInvariantChecker.cpp" .
