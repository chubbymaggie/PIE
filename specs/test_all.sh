#!/bin/bash

CGROUP="$1"

NUM_AVL_FUNS=12
NUM_LIS_FUNS=19
NUM_STR_FUNS=24

TESTS=6400
for CG_SIZE in "2" "16" "all" ; do
    echo -ne "\n\n\n ############ CG_SIZE = $CG_SIZE ############\n\n"

    echo > ../logs/$CGROUP/$TESTS/pie/$CG_SIZE/specs/list/RESULT
    for FINDEX in `seq 0 $(( NUM_LIS_FUNS - 1 ))`; do
        ./test.sh list.ml $FINDEX "$CGROUP" $TESTS $CG_SIZE
    done

    echo > ../logs/$CGROUP/$TESTS/pie/$CG_SIZE/specs/string/RESULT
    for FINDEX in `seq 0 $(( NUM_STR_FUNS - 1 ))`; do
        ./test.sh string.ml $FINDEX "$CGROUP" $TESTS $CG_SIZE
    done

    echo > ../logs/$CGROUP/$TESTS/pie/$CG_SIZE/specs/batavltree/RESULT
    for FINDEX in `seq 0 $(( NUM_AVL_FUNS - 1 ))`; do
        ./test.sh batavltree.ml $FINDEX "$CGROUP" $TESTS $CG_SIZE
    done
done

CG_SIZE=16
for TESTS in "1600" "3200" "12800" ; do
    echo -ne "\n\n\n ############ TESTS = $TESTS ############\n\n"

    echo > ../logs/$CGROUP/$TESTS/pie/$CG_SIZE/specs/list/RESULT
    for FINDEX in `seq 0 $((NUM_LIS_FUNS - 1 ))`; do
        ./test.sh list.ml $FINDEX "$CGROUP" $TESTS $CG_SIZE
    done

    echo > ../logs/$CGROUP/$TESTS/pie/$CG_SIZE/specs/string/RESULT
    for FINDEX in `seq 0 $(( NUM_STR_FUNS - 1))`; do
        ./test.sh string.ml $FINDEX "$CGROUP" $TESTS $CG_SIZE
    done

    echo > ../logs/$CGROUP/$TESTS/pie/$CG_SIZE/specs/batavltree/RESULT
    for FINDEX in `seq 0 $(( NUM_AVL_FUNS - 1 ))`; do
        ./test.sh batavltree.ml $FINDEX "$CGROUP" $TESTS $CG_SIZE
    done
done
