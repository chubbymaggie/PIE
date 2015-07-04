# Benchmarks from HOLA Paper (OOPSLA'13)

## Building
  - Single-loop programs have been modified to guarantee execution.
  - To print variables during runtime:
    - `#include "bm_oopsla.h"`
    - Use `INITIALIZE()` macro with a format string and the list of variables to be printed
    - Call `PRINT_VARS()` at program points where variables should be printed
    - Compile with `--std=c++11`

## Status

| Test                 | Invariant                                 | Remark                      |
| -------------------- | :---------------------------------------: | :-------------------------: |
| [00](00.cpp) | ![00_inv](http://mathurl.com/oc7ea3o.png) | :white_check_mark:          |
| [01](01.cpp) | ![01_inv](http://mathurl.com/nbdvhs3.png) | :white_check_mark:          |
| [02](02.cpp) | ![02_inv](http://mathurl.com/pa3ut8l.png) | :white_check_mark:          |
| [03](03.cpp) | ![03_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [04](04.cpp) | ![04_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [05](05.cpp) | ![05_inv](http://mathurl.com/o8uuce8.png) | :white_check_mark:          |
| [06](06.cpp) | ![06_inv](http://mathurl.com/oacrffn.png) | :white_check_mark:          |
| [07](07.cpp) | ![07_inv](http://mathurl.com/py8jd3p.png) | 3-CNF Expressiveness?       |
| [08](08.cpp) | ![08_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [09](09.cpp) | ![09_inv](http://mathurl.com/py8jd3p.png) | 3-CNF Expressiveness?       |
| [10](10.cpp) | ![10_inv](http://mathurl.com/qhodxgu.png) | :white_check_mark:          |
| [11](11.cpp) | ![11_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [12](12.cpp) | ![12_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [13](13.cpp) | ![13_inv](http://mathurl.com/py8jd3p.png) | Keeps trying                |
| [14](14.cpp) | ![14_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [15](15.cpp) | ![15_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [16](16.cpp) | ![16_inv](http://mathurl.com/py8jd3p.png) | Multiple loops              |
| [17](17.cpp) | ![17_inv](http://mathurl.com/ojo9lk9.png) | :white_check_mark:          |
| [18](18.cpp) | ![18_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [19](19.cpp) | ![19_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [20](20.cpp) | ![20_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [21](21.cpp) | ![21_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [22](22.cpp) | ![22_inv](http://mathurl.com/py8jd3p.png) | :boom: Explodes :boom:      |
| [23](23.cpp) | ![23_inv](http://mathurl.com/py8jd3p.png) | :boom: Explodes :boom:      |
| [24](24.cpp) | ![24_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [25](25.cpp) | ![25_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [26](26.cpp) | ![26_inv](http://mathurl.com/py8jd3p.png) | Keeps trying                |
| [27](27.cpp) | ![27_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [28](28.cpp) | ![28_inv](http://mathurl.com/pjbgymx.png) | :white_check_mark:          |
| [29](29.cpp) | ![29_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [30](30.cpp) | ![30_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [31](31.cpp) | ![31_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [32](32.cpp) | ![32_inv](http://mathurl.com/py8jd3p.png) | :boom: Explodes :boom:      |
| [33](33.cpp) | ![33_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [34](34.cpp) | ![34_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [35](35.cpp) | ![35_inv](http://mathurl.com/py8jd3p.png) | Break!                      |
| [36](36.cpp) | ![36_inv](http://mathurl.com/py8jd3p.png) | Multiple loops              |
| [37](37.cpp) | ![37_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [38](38.cpp) | ![38_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [39](39.cpp) | ![39_inv](http://mathurl.com/py8jd3p.png) | Break, Goto!                |
| [40](40.cpp) | ![40_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [41](41.cpp) | ![41_inv](http://mathurl.com/py8jd3p.png) | Multiple loops              |
