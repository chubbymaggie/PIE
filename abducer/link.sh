#!/bin/bash

cur="`pwd`"

root="`dirname \"$0\"`"
root="`cd $root && pwd`"

cd "../mistral/example/"
make all

cd "$cur/$1"

ln -fs "$root/specInferBase/escher_core.ml"         escher_core.ml
ln -fs "$root/specInferBase/escher_components.ml"   escher_components.ml
ln -fs "$root/specInferBase/escher_types.ml"        escher_types.ml
ln -fs "$root/specInferBase/escher_synth.ml"        escher_synth.ml

ln -fs "$root/specInferBase/specInfer.ml"   specInfer.ml
ln -fs "$root/specInferBase/top_helper.ml"  top_helper.ml
ln -fs "$root/specInferBase/makefile"       makefile

ln -fs "$root/../mistral/example/abduce"    abduce
ln -fs "$root/../mistral/example/chkSAT"    chkSAT
ln -fs "$root/../mistral/example/chkVALID"  chkVALID
ln -fs "$root/../mistral/example/simplify"  simplify
ln -fs "$root/../mistral/example/verify"    verify

ln -fs "$root/smt2ml.py"     smt2ml
ln -fs "$root/var_repl.py"   var_replace
ln -fs "$root/preprocess.py" preprocess
