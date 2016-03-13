#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

CGROUP="$1"
TIMEOUT="60m"

if hash timeout 2> /dev/null; then
  TMOUTDEF=''
else
  TMOUTDEF="function timeout() { perl -e 'alarm shift; exec @ARGV' \"$@\"; }"
  function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }
fi

LOCATION="../../logs/$CGROUP/pie/limit"
mkdir -p "$LOCATION" ; cd "$LOCATION"

ln -fs "$ROOT/../../base/escher_core.ml"         escher_core.ml
ln -fs "$ROOT/../../base/escher_components.ml"   escher_components.ml
ln -fs "$ROOT/../../base/escher_types.ml"        escher_types.ml
ln -fs "$ROOT/../../base/escher_synth.ml"        escher_synth.ml

ln -fs "$ROOT/../../base/pie.ml"         pie.ml
ln -fs "$ROOT/../../base/top_helper.ml"  top_helper.ml
ln -fs "$ROOT/../../base/makefile"       makefile

ln -fs "$ROOT/../../base/testGen.ml"     testGen.ml
ln -fs "$ROOT/../../base/postGen.ml"     postGen.ml
ln -fs "$ROOT/../../base/preprocess.py"  preprocess

ln -fs "$ROOT/PIE_limits.ml"             PIE_limits.ml
ln -fs "$ROOT/get_limits.sh"             get_limits

make -s clean ; make -s

ocamlfind ocamlopt -package qcheck -package batteries -w a -c "PIE_limits.ml"
ocamlfind ocamlopt -o "PIE_limits.e" -linkpkg -package qcheck -package batteries      \
                   testGen.cmx escher_types.cmx escher_core.cmx escher_components.cmx \
                   escher_synth.cmx pie.cmx "PIE_limits.cmx"

if [ "$?" -ne 0 ]; then exit 1; fi

for K in `seq 1 6`; do
  ./get_limits "$K" "$CGROUP" "$TIMEOUT"
done
