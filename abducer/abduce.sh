#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

USE_TOOL="$1"
SOURCE_FILE="$2"
RECORD_PREFIX="$3"

if [[ ! -f "$SOURCE_FILE" ]]; then
  echo "--- File $SOURCE_FILE doesn't exist. ABORT ---"
  exit 1
fi

TARGET="`dirname \"$SOURCE_FILE\"`"
FILE="`basename \"$SOURCE_FILE\"`"

"$ROOT/link.sh" "$TARGET"
cd "$TARGET"

make clean ; make

echo -ne "\n... $FILE ... \n"

# Simplify initial query
echo -ne "-\n-\n" > f
SIM_QUERY="`./simplify \"$FILE\"`"
echo "$SIM_QUERY" >> f
mv f "$FILE"

echo -ne "   [#] Simplified query: $SIM_QUERY\n" >&2

# MCF Query to OCaml code
./mcf2ml "$FILE" "$RECORD_PREFIX" "$USE_TOOL" > "$FILE.tml"
if [[ $? != 0 ]]; then
  echo "false" > "$FILE.sinf"
  exit 1
fi

./preprocess "$FILE.tml" > "T$FILE.ml" 2> /dev/null

# Compile OCaml code to binary
ocamlfind ocamlopt -package qcheck -package batteries -c "T$FILE.ml" 2>/dev/null
ocamlfind ocamlopt -o "$FILE.e" -linkpkg -package qcheck -package batteries            \
                                         testGen.cmx escher_types.cmx escher_core.cmx  \
                                         escher_components.cmx escher_synth.cmx        \
                                         specInfer.cmx "T$FILE.cmx" 2> /dev/null

# Replace variables & simplify
echo -ne "-\n-\n" > "$FILE.inf"
"./$FILE.e" | ./var_replace "$FILE.tml" >> "$FILE.inf"
./simplify "$FILE.inf" > "$FILE.sinf"
