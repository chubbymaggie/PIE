#!/bin/bash

FILE="`basename $1 .ml`"
FINDEX="$2"
CGROUP="$3"
TESTS="$4"
SZ_CONFLICT_SET="$5"

TOOL="pie"
TIMEOUT="60m"

if hash timeout 2> /dev/null; then
  TMOUTDEF=''
else
  TMOUTDEF="function timeout() { perl -e 'alarm shift; exec @ARGV' \"$@\"; }"
  function timeout() { perl -e 'alarm shift; exec @ARGV' "$@"; }
fi

if [[ "$CGROUP" == "" ]]; then
    LOCATION="../logs/$TESTS/$TOOL/$SZ_CONFLICT_SET/specs/$FILE"
else
    LOCATION="../logs/$CGROUP/$TESTS/$TOOL/$SZ_CONFLICT_SET/specs/$FILE"
fi

for PINDEX in `seq 0 1024`; do
    if [[ "$SZ_CONFLICT_SET" == "all" ]]; then
        ./setup.sh "$LOCATION" "$FILE.ml" 1000000000 $TESTS $FINDEX $PINDEX
    else
        ./setup.sh "$LOCATION" "$FILE.ml" $SZ_CONFLICT_SET $TESTS $FINDEX $PINDEX
    fi
    if [[ "$?" != "0" ]]; then break; fi

    echo -ne "#!/bin/bash\n\n$TMOUTDEF\n\nFILE=\"$FILE\"\nCGROUP=\"$CGROUP\"\nTIMEOUT=\"$TIMEOUT\"\n\n./compile.sh\n\n" > "$LOCATION/run_last_test.sh"
    tail -n 25 test.sh | head -n 22 >> "$LOCATION/run_last_test.sh"
    chmod +x "$LOCATION/run_last_test.sh"

    cd "$LOCATION"

    if [[ "$CGROUP" != "" ]]; then
        echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.failcnt
        echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.force_empty
        echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.memsw.max_usage_in_bytes
    fi

    if [[ "$CGROUP" == "" ]]; then
        timeout $TIMEOUT bash -c "bash -c 'time ./$FILE.e' 2>&1 | tee -a RESULT"
    else
        timeout $TIMEOUT bash -c "bash -c 'time cgexec -g memory,cpu:$CGROUP ./$FILE.e' 2>&1 | tee -a RESULT"
    fi

    LASTLINE="`tail -n 5 RESULT | head -n 1`"
    if [[ "$LASTLINE" == 'Fatal error: exception Invalid_argument("Index past end of list")' ]]; then break; fi

    if [[ "$CGROUP" != "" ]]; then
        echo -ne "\n[M]ax Memory Usage = " 2>&1 | tee -a RESULT
        echo $(( $(cat /sys/fs/cgroup/memory/$CGROUP/memory.memsw.max_usage_in_bytes) / (1024 * 1024) )) 2>&1 | tee -a RESULT
        echo -ne "\n\n" 2>&1 | tee -a RESULT
    fi

    ./clean RESULT

    cd ~-
done
