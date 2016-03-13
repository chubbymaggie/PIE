#!/bin/bash

CGROUP="$1"

NUM_AVL_FUNS=12
NUM_LIS_FUNS=19
NUM_STR_FUNS=24


FIX_TESTS=6400
ALL_CG_SIZES="2 16 all"

for CG_SIZE in "$ALL_CG_SIZES" ; do
    echo -ne "\n\n\n ############ CG_SIZE = $CG_SIZE ############\n\n"

    echo > ../logs/$CGROUP/$FIX_TESTS/pie/$CG_SIZE/specs/list/RESULT
    for FINDEX in `seq 0 $(( NUM_LIS_FUNS - 1 ))`; do
        ./test.sh list.ml $FINDEX "$CGROUP" $FIX_TESTS $CG_SIZE
    done

    echo > ../logs/$CGROUP/$FIX_TESTS/pie/$CG_SIZE/specs/string/RESULT
    for FINDEX in `seq 0 $(( NUM_STR_FUNS - 1 ))`; do
        ./test.sh string.ml $FINDEX "$CGROUP" $FIX_TESTS $CG_SIZE
    done

    echo > ../logs/$CGROUP/$FIX_TESTS/pie/$CG_SIZE/specs/batavltree/RESULT
    for FINDEX in `seq 0 $(( NUM_AVL_FUNS - 1 ))`; do
        ./test.sh batavltree.ml $FINDEX "$CGROUP" $FIX_TESTS $CG_SIZE
    done
done

exit 0 #########################################################################

FIX_CG_SIZE=16
OTHER_TESTS="1600 3200 12800"

for TESTS in "$OTHER_TESTS" ; do
    echo -ne "\n\n\n ############ TESTS = $TESTS ############\n\n"

    echo > ../logs/$CGROUP/$TESTS/pie/$FIX_CG_SIZE/specs/list/RESULT
    for FINDEX in `seq 0 $((NUM_LIS_FUNS - 1 ))`; do
        ./test.sh list.ml $FINDEX "$CGROUP" $TESTS $FIX_CG_SIZE
    done

    echo > ../logs/$CGROUP/$TESTS/pie/$FIX_CG_SIZE/specs/string/RESULT
    for FINDEX in `seq 0 $(( NUM_STR_FUNS - 1))`; do
        ./test.sh string.ml $FINDEX "$CGROUP" $TESTS $FIX_CG_SIZE
    done

    echo > ../logs/$CGROUP/$TESTS/pie/$FIX_CG_SIZE/specs/batavltree/RESULT
    for FINDEX in `seq 0 $(( NUM_AVL_FUNS - 1 ))`; do
        ./test.sh batavltree.ml $FINDEX "$CGROUP" $TESTS $FIX_CG_SIZE
    done
done
