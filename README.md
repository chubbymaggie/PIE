# PIE
A tool to infer specifications for OCaml programs.

## System Requirements
  - [CVC4](https://github.com/CVC4/CVC4)
    - CVC4 runs into a GCC bug when compiled with the latest GCC 5.2.1
    - Compiles fine with GCC 4.9, so I use `CC=gcc-4.9 CXX=g++4.9 ./configure ...`
  - [Z3-str2](https://github.com/z3str/Z3-str)
  - `OCaml` with the following libraries:
    - `batteries`
    - `qcheck`

## Precondition Inference for OCaml code
All the tests presented in PLDI paper are in `specs`.
- To run all tests, just run `./test_all.sh`, with an optional `<CGROUP_NAME>`.
- To run a specific test (all postconditions for a specific function),
  run `./test.sh` as:
  - e.g. `./test.sh <TEST_FILE> <TEST_FUNC_ID> <CGROUP_NAME> <MAX_TESTS> <SZ_CONFLICT_SET>`
  - `TEST_FILE` = `string.ml`
  - `TEST_FUNC_ID` = 3
  - `CGROUP_NAME` = `my_cg` (Optional, can be `""`)
  - `MAX_TESTS` = `6400`
  - `SZ_CONFLICT_SET` = `16`
- To run a specific postcondition for a specific function, change the `PINDEX` within
  `test.sh` and run as before.

## Loop Invariant Inference for C++ code
### Setup
  - Checkout LLVM (with Clang) to `/my_root/path/to/llvm`
  - Run `./setup.sh` under `ClangTool` directory as:
    - e.g. `./setup.sh <LLVM_ROOT>`
    - `LLVM_ROOT` = `/my_root/path/to/llvm`
  - For evaluating under a Linux `cgroup` (not to be confused with conflict groups):
    - add `swapaccount=1` to your linux kernel parameters:
      - Under Ubuntu with GRUB, add it to `GRUB_CMDLINE_LINUX` in `/etc/default/grub`
      - run `update-grub` and reboot
    - modify the `setup.sh` in `ClangTool` to set the required limits on memory / cpu usage
    - run `./setup.sh` under `ClangTool` as:
      - e.g. `./setup.sh <LLVM_ROOT> <CGROUP_NAME>`
      - `LLVM_ROOT` = `/my_root/path/to/llvm`
      - `CGROUP_NAME` = `my_cg`

Integer benchmarks are in `bm_oopsla`, and String benchmarks are in `bm_strings`.
- To test a particular benchmark, run `./checker` under `/my_root/path/to/llvm/build` as:
  - e.g. `./checker <TEST_FILE> <MAX_TESTS> <TOOL> <CGROUP_NAME> <SZ_CONFLICT_SET>`
  - `TEST_FILE` = `/my_root/path/to/PIE/bm_strings/cav2014d.cpp`
  - `MAX_TESTS` = `6400`
  - `TOOL` = `pie` (can be `pie` or `escher`)
  - `CGROUP_NAME` = `my_cg` (Optional, can be `""`)
  - `SZ_CONFLICT_SET` = `16`
