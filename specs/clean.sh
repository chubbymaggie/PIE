#!/bin/bash

_=`vim -e -s -c ':set noro' -c ':%s/\r//ge' \
       -c ':%s/\ \ \ \ \[%\] Inferring .*(\(.*\)f.*).*\n\(\ \ \ \ \[%\] Inferring\)\@!\(p.\+\n\)\{,2}/[S]ynthesized feaures = \1\r\r/ge' \
       -c ':%s/\ \ \ \ \[%\].*\n//ge' -c ':%s/===.*\nFatal\(.*\n\)\{5}//ge' -c ':w! TEMPX' -c ':qa!' $1`
cat -s TEMPX > $1.clean
