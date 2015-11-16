#!/bin/bash

ROOT="`dirname \"$0\"`"
ROOT="`cd \"$ROOT\" && pwd`"

TARGET="`[[ -d \"$1\" ]] || mkdir -p \"$1\" && cd \"$1\" && pwd`"

FILE="`realpath \"$2\"`"
FILENAME="`basename \"$FILE\" .ml`"

cd "$TARGET"

ln -fs "$FILE" "$FILENAME.ml"
perl -pe 's#__MAX_CONFLICT_SET_SIZE__#'"$3"'#g' < "$FILE" > "t$FILENAME.ml"
perl -pi -e 's#__TEST_SIZE__#'"$4"'#g' "t$FILENAME.ml"
perl -pi -e 's#__FUNCTION_INDEX__#'"$5"'#g' "t$FILENAME.ml"
perl -pi -e 's#__POST_INDEX__#'"$6"'#g' "t$FILENAME.ml"

ln -fs "$ROOT/../base/escher_core.ml"         escher_core.ml
ln -fs "$ROOT/../base/escher_components.ml"   escher_components.ml
ln -fs "$ROOT/../base/escher_types.ml"        escher_types.ml
ln -fs "$ROOT/../base/escher_synth.ml"        escher_synth.ml

ln -fs "$ROOT/../base/specInfer.ml"   specInfer.ml
ln -fs "$ROOT/../base/top_helper.ml"  top_helper.ml
ln -fs "$ROOT/../base/makefile"       makefile

ln -fs "$ROOT/../base/testGen.ml"     testGen.ml
ln -fs "$ROOT/../base/postGen.ml"     postGen.ml
ln -fs "$ROOT/../base/preprocess.py"  preprocess

ln -fs "$ROOT/clean.sh"     clean

./preprocess "t$FILENAME.ml" ALL > "T$FILENAME.ml"

make -s clean ; make -s

echo -ne "#!/bin/bash\n\nFILENAME=\"$FILENAME\"\n\n" > compile.sh
tail -n 4 "$ROOT/setup.sh" >> compile.sh
chmod +x compile.sh

ocamlfind ocamlopt -package qcheck -package batteries -w a -c "T$FILENAME.ml"
ocamlfind ocamlopt -o "$FILENAME.e" -linkpkg -package qcheck -package batteries       \
                   testGen.cmx escher_types.cmx escher_core.cmx escher_components.cmx \
                   escher_synth.cmx specInfer.cmx "T$FILENAME.cmx"
