#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

TARGET="`cd \"$1\" && pwd`"

cd "$ROOT/../mistral/example/"
make all

cd "$TARGET"

ln -fs "$ROOT/specInferBase/escher_core.ml"         escher_core.ml
ln -fs "$ROOT/specInferBase/escher_components.ml"   escher_components.ml
ln -fs "$ROOT/specInferBase/escher_types.ml"        escher_types.ml
ln -fs "$ROOT/specInferBase/escher_synth.ml"        escher_synth.ml

ln -fs "$ROOT/specInferBase/specInfer.ml"   specInfer.ml
ln -fs "$ROOT/specInferBase/top_helper.ml"  top_helper.ml
ln -fs "$ROOT/specInferBase/makefile"       makefile

ln -fs "$ROOT/../mistral/example/abduce"    abduce
ln -fs "$ROOT/../mistral/example/chkSAT"    chkSAT
ln -fs "$ROOT/../mistral/example/chkVALID"  chkVALID
ln -fs "$ROOT/../mistral/example/simplify"  simplify
ln -fs "$ROOT/../mistral/example/verify"    verify

ln -fs "$ROOT/replay.sh"     replay
ln -fs "$ROOT/smt2ml.py"     smt2ml
ln -fs "$ROOT/var_repl.py"   var_replace
ln -fs "$ROOT/preprocess.py" preprocess
