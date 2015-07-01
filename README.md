# specInfer
A tool to infer specifications for OCaml programs.

## Setup
 - Checkout LLVM (with Clang) to `/my_root/path/to/llvm`
 - Run `./Clang_Checker/setup.sh` with the following parameters (in order):
    - `my_root/path/to/llvm/tools/Clang`
    - `my_root/path/to/mistral`
    - `my_root/path/to/abducer`

## Status

| Test                 | Invariant                                 | Remark                      |
| -------------------- | :---------------------------------------: | :-------------------------: |
| [00](bm_oopsla/00.c) | ![00_inv](http://mathurl.com/oc7ea3o.png) | :white_check_mark:          |
| [01](bm_oopsla/01.c) | ![01_inv](http://mathurl.com/nbdvhs3.png) | :white_check_mark:          |
| [02](bm_oopsla/02.c) | ![02_inv](http://mathurl.com/pa3ut8l.png) | :white_check_mark:          |
| [03](bm_oopsla/03.c) | ![03_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [04](bm_oopsla/04.c) | ![04_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [05](bm_oopsla/05.c) | ![05_inv](http://mathurl.com/o8uuce8.png) | :white_check_mark:          |
| [06](bm_oopsla/06.c) | ![06_inv](http://mathurl.com/oacrffn.png) | :white_check_mark:          |
| [07](bm_oopsla/07.c) | ![07_inv](http://mathurl.com/py8jd3p.png) | 3-CNF Expressiveness?       |
| [08](bm_oopsla/08.c) | ![08_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [09](bm_oopsla/09.c) | ![09_inv](http://mathurl.com/py8jd3p.png) | 3-CNF Expressiveness?       |
| [10](bm_oopsla/10.c) | ![10_inv](http://mathurl.com/qhodxgu.png) | :white_check_mark:          |
| [11](bm_oopsla/11.c) | ![11_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [12](bm_oopsla/12.c) | ![12_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [13](bm_oopsla/13.c) | ![13_inv](http://mathurl.com/py8jd3p.png) | Keeps trying                |
| [14](bm_oopsla/14.c) | ![14_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [15](bm_oopsla/15.c) | ![15_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [16](bm_oopsla/16.c) | ![16_inv](http://mathurl.com/py8jd3p.png) | Multiple loops              |
| [17](bm_oopsla/17.c) | ![17_inv](http://mathurl.com/ojo9lk9.png) | :white_check_mark:          |
| [18](bm_oopsla/18.c) | ![18_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [19](bm_oopsla/19.c) | ![19_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [20](bm_oopsla/20.c) | ![20_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [21](bm_oopsla/21.c) | ![21_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [22](bm_oopsla/22.c) | ![22_inv](http://mathurl.com/py8jd3p.png) | :boom: Explodes :boom:      |
| [23](bm_oopsla/23.c) | ![23_inv](http://mathurl.com/py8jd3p.png) | :boom: Explodes :boom:      |
| [24](bm_oopsla/24.c) | ![24_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [25](bm_oopsla/25.c) | ![25_inv](http://mathurl.com/py8jd3p.png) | :boom: >6-CNF?? :boom:      |
| [26](bm_oopsla/26.c) | ![26_inv](http://mathurl.com/py8jd3p.png) | Keeps trying                |
| [27](bm_oopsla/27.c) | ![27_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [28](bm_oopsla/28.c) | ![28_inv](http://mathurl.com/pjbgymx.png) | :white_check_mark:          |
| [29](bm_oopsla/29.c) | ![29_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [30](bm_oopsla/30.c) | ![30_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [31](bm_oopsla/31.c) | ![31_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [32](bm_oopsla/32.c) | ![32_inv](http://mathurl.com/py8jd3p.png) | :boom: Explodes :boom:      |
| [33](bm_oopsla/33.c) | ![33_inv](http://mathurl.com/py8jd3p.png) | Non-deterministic condition |
| [34](bm_oopsla/34.c) | ![34_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [35](bm_oopsla/35.c) | ![35_inv](http://mathurl.com/py8jd3p.png) | Break!                      |
| [36](bm_oopsla/36.c) | ![36_inv](http://mathurl.com/py8jd3p.png) | Multiple loops              |
| [37](bm_oopsla/37.c) | ![37_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [38](bm_oopsla/38.c) | ![38_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [39](bm_oopsla/39.c) | ![39_inv](http://mathurl.com/py8jd3p.png) | Break, Goto!                |
| [40](bm_oopsla/40.c) | ![40_inv](http://mathurl.com/py8jd3p.png) | Nested loops                |
| [41](bm_oopsla/41.c) | ![41_inv](http://mathurl.com/py8jd3p.png) | Multiple loops              |
