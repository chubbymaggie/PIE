#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

TARGET="`cd \"$1\" && pwd`"

FILE="`realpath \"$2\"`"

cd "$TARGET"

ln -fs "$FILE" "`basename \"$FILE\"`"

ln -fs "$ROOT/../base/escher_core.ml"         escher_core.ml
ln -fs "$ROOT/../base/escher_components.ml"   escher_components.ml
ln -fs "$ROOT/../base/escher_types.ml"        escher_types.ml
ln -fs "$ROOT/../base/escher_synth.ml"        escher_synth.ml

ln -fs "$ROOT/../base/specInfer.ml"   specInfer.ml
ln -fs "$ROOT/../base/top_helper.ml"  top_helper.ml
ln -fs "$ROOT/../base/makefile"       makefile

ln -fs "$ROOT/../base/specify.ml"     specify.ml
ln -fs "$ROOT/../base/preprocess.py"  preprocess
