# specInfer
A tool to infer specifications for OCaml programs.

## Setup
  - Checkout LLVM (with Clang) to `/my_root/path/to/llvm`
  - Run `./Clang_Checker/setup.sh` with the following parameters (in order):
    - `my_root/path/to/llvm/tools/Clang`
    - `my_root/path/to/mistral`
    - `my_root/path/to/abducer`

## Status
  - [HOLA Benchmarks (OOPSLA'13)](bm_oopsla/)
