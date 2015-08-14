#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

TARGET="`cd \"$1\" && pwd`"

cd "$TARGET"

ln -fs "$ROOT/../base/escher_core.ml"         escher_core.ml
ln -fs "$ROOT/../base/escher_components.ml"   escher_components.ml
ln -fs "$ROOT/../base/escher_types.ml"        escher_types.ml
ln -fs "$ROOT/../base/escher_synth.ml"        escher_synth.ml

ln -fs "$ROOT/../base/specify.ml"     specify.ml
ln -fs "$ROOT/../base/specInfer.ml"   specInfer.ml
ln -fs "$ROOT/../base/top_helper.ml"  top_helper.ml
ln -fs "$ROOT/../base/makefile"       makefile

ln -fs "$ROOT/../base/testGen.ml"     testGen.ml
ln -fs "$ROOT/../base/preprocess.py"  preprocess

# Solvers:
#
#  Mistral : (mistral)
#  Z3      : (z3)
#  CVC4    : (cvc4)

SOLVER="cvc4"

EXT=""
if [ "$SOLVER" != "mistral" ]; then
  EXT=".py"
  ln -fs "$ROOT/../$SOLVER/mcf2smtlib$EXT"  mcf2smtlib.py
else
  cd "$ROOT/../mistral"
  make
  cd "$TARGET"
fi

ln -fs "$ROOT/../$SOLVER/chkSAT$EXT"      chkSAT
ln -fs "$ROOT/../$SOLVER/chkVALID$EXT"    chkVALID
ln -fs "$ROOT/../$SOLVER/simplify$EXT"    simplify
ln -fs "$ROOT/../$SOLVER/verify$EXT"      verify

ln -fs "$ROOT/replay.sh"        replay
ln -fs "$ROOT/smt2ml.py"        smt2ml
ln -fs "$ROOT/var_repl.py"      var_replace
ln -fs "$ROOT/add_counter.py"   add_counter
