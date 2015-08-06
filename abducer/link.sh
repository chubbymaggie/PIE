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

ln -fs "$ROOT/../z3/mcf2smtlib.py"  mcf2smtlib.py
ln -fs "$ROOT/../z3/chkSAT.py"      chkSAT
ln -fs "$ROOT/../z3/chkVALID.py"    chkVALID
ln -fs "$ROOT/../z3/simplify.py"    simplify
ln -fs "$ROOT/../z3/verify.py"      verify

ln -fs "$ROOT/replay.sh"        replay
ln -fs "$ROOT/smt2ml.py"        smt2ml
ln -fs "$ROOT/var_repl.py"      var_replace
ln -fs "$ROOT/add_counter.py"   add_counter
