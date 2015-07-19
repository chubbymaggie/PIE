#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

if [[ ! -f "$1" ]]; then
  echo "--- File $1 doesn't exist. ABORT ---"
  exit 1
fi

TARGET="`dirname \"$1\"`"
FILE="`basename \"$1\"`"

"$ROOT/link.sh" "$TARGET"
cd "$TARGET"

make cleaner ; make

echo -ne "\n... $FILE ... \n"

# Simplify initial query
echo -ne "-\n-\n" > f
SIM_QUERY="`./simplify \"$FILE\"`"
echo "$SIM_QUERY" >> f
mv f "$FILE"

echo -ne "   [#] Simplified query: $SIM_QUERY\n" >&2

# MCF Query to OCaml code
./smt2ml "$FILE" > "$FILE.tml"
if [[ $? != 0 ]]; then
  echo "false" > "$FILE.sinf"
  exit 1
fi

./preprocess "$FILE.tml" > "T$FILE.ml"

# Compile OCaml code to binary
ocamlfind ocamlopt -package batteries -c "T$FILE.ml" 2>/dev/null
ocamlfind ocamlopt -o "$FILE.e" -linkpkg -package batteries escher_*.cmx specInfer.cmx "T$FILE.cmx" 2> /dev/null

# Replace variables & simplify
echo -ne "-\n-\n" > "$FILE.inf"
"./$FILE.e" | ./var_replace "$FILE.tml" >> "$FILE.inf"
./simplify "$FILE.inf" > "$FILE.sinf"
