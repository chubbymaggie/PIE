#!/bin/bash

old_dir=`pwd`
cur_time=$(date "+%Y.%m.%d-%H.%M.%S")
file="infer-test.$cur_time"

./link.sh "$1"
cd "$1"

make
echo '' > "$file"

printf "\n\n %-24s\t%-6s\tSMT\tPRE\n" "FILE_PATH" "SIZE"

for f in *.mcf
do
    printf "+ Processing :: $f ..."
    sz=`wc -c < $f`
    $old_dir/smt2ml.py $f > $f.tml ; cres="$?"
    $old_dir/../preprocess.py $f.tml > T$f.ml ; tres="$?"
    printf "\r%164s\r+ Compiling :: T$f.ml ..."
    ocamlfind ocamlopt -package batteries -c T$f.ml
    ocamlfind ocamlopt -o $f.e -linkpkg -package batteries escher_*.cmx specInfer.cmx T$f.cmx
    printf "\r%164s\r+ SpecInfer-ing :: $f.e ..."
    our_res=`echo -ne "-\n-\n" > $f.sinf ; ./$f.e | $old_dir/var_repl.py $f.tml`
    our_sres=`echo "$our_res" >> $f.sinf ; ./simplify $f.sinf`
    printf "\r%164s\r+ Simplifying-ing :: $f ..."
    sim_res=`./simplify $f`
    printf "\r%164s\r+ Mistral-ing :: $f ..."
    their_res=`./abduce $f`
    query=`cat $f | tail -n 1`
    printf "\n\n\n%s\n%8s\t%s\n\n%8s\t%s\n%8s\t%s\n\n%8s\t%s\n%8s\t%s\n" "$f" "QUERY" "$query" "SINFER" "$our_res" "S-SIMPLE" "$our_sres" "SIMPLE" "$sim_res" "ABDUCE" "$their_res" >> "$file"
    printf "\r%164s\r %-24s\t%-6s\t$cres\t$tres\n" "" "$f" "$sz"
done

cd "$old_dir"
