#!/bin/bash

if [[ ! -f "$1" ]]; then
  exit 1
fi

FILE="$1"

make clean ; make

echo -ne "\n... $FILE ... \n"

# Just verify SAT, use old .tml
./smt2ml "$FILE" > "/tmp/$FILE.tml"
if [[ $? != 0 ]]; then
  echo "false" > "$FILE.sinf"
  exit 1
fi

./preprocess "$FILE.tml" > "T$FILE.ml" 2> /dev/null

# Compile OCaml code to binary
ocamlfind ocamlopt -package batteries -c "T$FILE.ml" 2>/dev/null
ocamlfind ocamlopt -o "$FILE.e" -linkpkg -package batteries escher_*.cmx specInfer.cmx "T$FILE.cmx" 2> /dev/null

# Replace variables & simplify
echo -ne "-\n-\n" > "$FILE.inf"
"./$FILE.e" | ./var_replace "$FILE.tml" >> "$FILE.inf"
./simplify "$FILE.inf" > "$FILE.sinf"
