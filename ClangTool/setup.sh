#!/bin/bash

if [[ $# -lt 1 ]]; then
  echo "Please provide path to LLVM_ROOT"
  exit 1
fi

OWN_ROOT="`dirname "$0"`"
OWN_ROOT="`cd \"$OWN_ROOT\" && pwd`"

LLVM_ROOT="`cd \"$1\" && pwd`"
ABDUCER_ROOT="`cd ../abducer/ && pwd`"
WORKING_ROOT="`cd ../logs/ || mkdir -p ../logs/ && pwd`"

cd "$LLVM_ROOT/tools/clang/tools"

NEW_TARGET_LINE="add_subdirectory(pinvgen)"
if [[ "`tail -n 1 < CMakeLists.txt`" != "$NEW_TARGET_LINE" ]]; then
  echo "$NEW_TARGET_LINE" >> CMakeLists.txt
fi

cp -Rf "$OWN_ROOT/pinvgen" .
cd "$LLVM_ROOT" ; mkdir build ; cd build

perl -pe 's#__WORKING_PATH_BASE_FROM_SETUP_SCRIPT__#'"$WORKING_ROOT"'#g' < "$OWN_ROOT/checker.template.sh" > checker
perl -pi -e 's#__ABDUCER_PATH_FROM_SETUP_SCRIPT__#'"$ABDUCER_ROOT"'#g' checker
chmod +x checker

perl -pe 's#__ABDUCER_PATH_FROM_SETUP_SCRIPT__#'"$ABDUCER_ROOT"'#g' < "$OWN_ROOT/check_all.template.sh" > check_all_with_config
chmod +x check_all_with_config

# We need to make everything, not just pinvgen; because Clang uses so internal
# headers etc. which are produced after a full make
cmake .. && make -j4
