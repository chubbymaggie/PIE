#!/bin/bash

K="$1"
CGROUP="$2"
TIMEOUT="$3"

printf "Checking K = $K:\n"

MIN=1
MAX=524288
OLDF=0
while true; do
  echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.failcnt
  echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.force_empty
  echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.memsw.failcnt
  echo 0 > /sys/fs/cgroup/memory/$CGROUP/memory.memsw.max_usage_in_bytes

  F=$(( ($MIN + $MAX + 1) / 2 ))
  if [ "$F" == "$OLDF" ]; then break; fi
  printf "  . [$MIN] $F [$MAX]\n"

  timeout $TIMEOUT bash -c "cgexec -g memory,cpu:$CGROUP ./PIE_limits.e '$K' '$F' &> /dev/null"
  RET="$?"

  FAIL=`cat /sys/fs/cgroup/memory/$CGROUP/memory.memsw.failcnt`
  if [ "$RET" -ne 0 ] || [ "$FAIL" -gt 0 ]; then MAX="$F"; else MIN="$F"; fi

  OLDF=$F
done

if [ "$MIN" -ne "$MAX" ]; then F=$MIN; fi
echo -ne "PIE_Limit($K) = $F\n\n\n"
