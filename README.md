# specInfer
A tool to infer specifications for OCaml programs.

## Setup
  - Checkout LLVM (with Clang) to `/my_root/path/to/llvm`
  - Run `./Clang_Checker/setup.sh` with the following parameters (in order):
    - Clang root: `my_root/path/to/llvm/tools/Clang`
    - Working root: (this is where all logs would be generated at run time) `my_root/path/to/abducer_logs`

## Status
  - [HOLA Benchmarks (OOPSLA'13)](bm_oopsla/)
