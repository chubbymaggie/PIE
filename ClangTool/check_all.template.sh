#!/bin/bash

for TEST_FILE in __ABDUCER_PATH_FROM_SETUP_SCRIPT__/../bm_{oopsla,strings}/*.cpp ; do
    echo "[+] Checking $TEST_FILE ..."
    ./checker $TEST_FILE $@ &> /dev/null
done
