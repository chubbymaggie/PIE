#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

TARGET="`cd \"$1\" && pwd`"

cd "$TARGET"

ln -fs "$ROOT/../base/escher_core.ml"         escher_core.ml
ln -fs "$ROOT/../base/escher_components.ml"   escher_components.ml
ln -fs "$ROOT/../base/escher_types.ml"        escher_types.ml
ln -fs "$ROOT/../base/escher_synth.ml"        escher_synth.ml

ln -fs "$ROOT/../base/pie.ml"         pie.ml
ln -fs "$ROOT/../base/top_helper.ml"  top_helper.ml
ln -fs "$ROOT/../base/makefile"       makefile

ln -fs "$ROOT/../base/postGen.ml"     postGen.ml
ln -fs "$ROOT/../base/testGen.ml"     testGen.ml
ln -fs "$ROOT/../base/preprocess.py"  preprocess

# Solvers:

#SOLVER="z3"
#SOLVER="cvc4"
SOLVER="hybrid"

ln -fs "$ROOT/../$SOLVER/chkSAT.py"      chkSAT
ln -fs "$ROOT/../$SOLVER/chkVALID.py"    chkVALID
ln -fs "$ROOT/../$SOLVER/simplify.py"    simplify
ln -fs "$ROOT/../$SOLVER/verify.py"      verify

ln -fs "$ROOT/mcf2ml.py"           mcf2ml
ln -fs "$ROOT/mcf2xml.py"          mcf2xml
ln -fs "$ROOT/var_repl.py"         var_replace
ln -fs "$ROOT/add_counter.py"      add_counter
ln -fs "$ROOT/remove_ambiguous.py" remove_ambiguous
ln -fs "$ROOT/separate_tests.py"   separate_tests
