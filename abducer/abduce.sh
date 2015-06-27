#!/bin/bash

./link.sh "$1"
cd "$1"

make clean ; make

for f in *.mcf
do
    echo -ne "\n... $f ... \n"

    echo -ne "-\n-\n" > f
    ./simplify $f >> f
    mv f $f

    ./smt2ml $f > $f.tml ; cres="$?"

    ./preprocess $f.tml > T$f.ml ; tres="$?"

    ocamlfind ocamlopt -package batteries -c T$f.ml 2>/dev/null
    ocamlfind ocamlopt -o $f.e -linkpkg -package batteries escher_*.cmx specInfer.cmx T$f.cmx 2> /dev/null

    echo -ne "-\n-\n" > $f.inf
    ./$f.e | ./var_replace $f.tml >> $f.inf
    ./simplify $f.inf > $f.sinf
done
