#!/bin/bash

TESTS=6400
for CG_SIZE in "2" "16" "all" ; do
    echo -ne "\n\n\n ############ CG_SIZE = $CG_SIZE ############\n\n"

    echo > ../logs/mem8gb/$TESTS/pie/$CG_SIZE/specs/list/RESULT
    for FINDEX in `seq 0 14`; do
        ./test.sh list.ml $FINDEX mem8gb $TESTS pie $CG_SIZE
    done

    echo > ../logs/mem8gb/$TESTS/pie/$CG_SIZE/specs/string/RESULT
    for FINDEX in `seq 0 21`; do
        ./test.sh string.ml $FINDEX mem8gb $TESTS pie $CG_SIZE
    done

    echo > ../logs/mem8gb/$TESTS/pie/$CG_SIZE/specs/batavltree/RESULT
    for FINDEX in `seq 0 10`; do
        ./test.sh batavltree.ml $FINDEX mem8gb $TESTS pie $CG_SIZE
    done
done

CG_SIZE=16
for TESTS in "1600" "3200" "12800" ; do
    echo -ne "\n\n\n ############ TESTS = $TESTS ############\n\n"

    echo > ../logs/mem8gb/$TESTS/pie/$CG_SIZE/specs/list/RESULT
    for FINDEX in `seq 0 14`; do
        ./test.sh list.ml $FINDEX mem8gb $TESTS pie $CG_SIZE
    done

    echo > ../logs/mem8gb/$TESTS/pie/$CG_SIZE/specs/string/RESULT
    for FINDEX in `seq 0 21`; do
        ./test.sh string.ml $FINDEX mem8gb $TESTS pie $CG_SIZE
    done

    echo > ../logs/mem8gb/$TESTS/pie/$CG_SIZE/specs/batavltree/RESULT
    for FINDEX in `seq 0 10`; do
        ./test.sh batavltree.ml $FINDEX mem8gb $TESTS pie $CG_SIZE
    done
done
