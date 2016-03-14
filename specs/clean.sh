#!/bin/bash

_=`vim -e -s -c ':set noro' \
             -c ':%s/\r//ge' \
             -c ':%s/\ \ \ \ \[%\] Removing conflicts.*@\(\d\+\)(\(\d\+\) explored).*/+ Explored \2 ASTs till size \1/ge' \
             -c ':%s/\ \ \ \ \[%\] Inferring .* \[k = \(\d\+\)\] (\(.*\)f.*).*\n\(\ \ \ \ \[%\] Inferring\)\@!\(p.\+\n\)\{,2}/+ K-CNF = \1+ Synthesized features = \2/ge' \
             -c ':%s/\ \ \ \ \[%\].*\n//ge' \
             -c ':%s/===.*\nFatal\(.*\n\)\{5}//ge' \
          -c ':w! TEMPX' \
          -c ':qa!' $1`
cat -s TEMPX > $1.clean
