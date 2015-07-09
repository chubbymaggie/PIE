# specInfer
A tool to infer specifications for OCaml programs.

## Setup
  - Checkout LLVM (with Clang) to `/my_root/path/to/llvm`
  - Run `./Clang_Checker/setup.sh` with the following parameter:
    - LLVM root: `my_root/path/to/llvm`

## Status
  - [HOLA Benchmarks (OOPSLA'13)](bm_oopsla/)

## Notes
  - 6th July Meeting
    - [#7](../../issues/7) Determine if conjoining abductive solutions is necessary
    - [#8](../../issues/8) Add a counter-example instead of aborting on `{pre}` check
    - Generality of specInfer: Does not need (complete) specification of pre-condition. It can learn
      a subset of the pre-condition, from the provided tests.
