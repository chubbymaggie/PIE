# PIE #
A tool to infer precondition for OCaml programs.

## <i class="fa fa-fw fa-cogs" id="setting-up-the-vm"></i> Setting up the VM
----------------------------------------------------------------------------

1. Download the .ova VM image.
2. Import into your favorite virtualization software.
   ([Instructions for VirtualBox](https://www.virtualbox.org/manual/ch01.html#ovf))
3. Boot and follow on-screen instructions.

**Note:**
- Default Username = Default Password = <kbd>pie</kbd>
- `~/Repos` is symlinked to `~/Desktop/Repos` for convenience
- Internet access is not necessary, but might be useful when running the VM.
- **Please have at least 18GB of free space, before importing the .ova image.**  
The .ova image is ~2GB, but expands to ~8GB when imported. The actual
.vmdk virtual harddisk is a dynamically allocated disk and may expand up to ~16GB
depending on usage. Please make sure that you have sufficient available disk space!

You may skip directly to [overview of tests](#overview-of-tests).



## <i class="fa fa-fw fa-wrench" id="manual-setup"></i> Manual Setup
--------------------------------------------------------------------

### Environment & Compilers
- System packages
  - Bash
  - Python 2, Python 3
  - OCaml 4.0+
- Sources (for building our Clang tool)
  - LLVM
  - Clang
- Libraries
  - `pyparsing` (for Python)
  - `batteries` (for OCaml)
  - `qcheck` (for OCaml)
- Constraint solvers
  - [Z3Str2](https://github.com/z3str/Z3-str)
  - [CVC4](https://github.com/CVC4/CVC4)

**Note:**  
  - PIE assumes that the binaries for the constraint solvers are in your `$PATH`.



## <i class="fa fa-fw fa-table" id="overview-of-tests"></i> Overview of Tests
-----------------------------------------------------------------------------

### Configurations
A configuration is defined by the two parameters:
- number of tests generated
- maximum size of the conflict group for the synthesizer

We evaluated our tool on:
- number of tests ranging over {1600, 3200, 6400, 12800}
- maximum size of conflict group ranging over {2, 16, _all_ <sup>#</sup>}

<sup>#</sup> _all_ refers to the case where we pass the entire conflict group to the synthesizer.

### Parameter Selection
As described in the paper, we test the following configurations for our 2 sets of experiments:
- Precondition Inference:
  - Varying sizes of conflict groups: {6400} x {2, 16, _all_ }
  - Varying number of tests: {1600, 3200, 6400, 12800} x {16}
- Loop Invariant Inference: &lt;6400, 16&gt;

### Tests in PLDI Submission

- **Precondition Inference** (for all first order functions from these OCaml modules)
  - [batavltree.ml](https://github.com/SaswatPadhi/PIE/blob/master/specs/batavltree.ml)
    for [BatAvlTree](http://ocaml-batteries-team.github.io/batteries-included/hdoc2/BatAvlTree.html)
  - [list.ml](https://github.com/SaswatPadhi/PIE/blob/master/specs/list.ml)
    for [List](http://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html)
  - [string.ml](https://github.com/SaswatPadhi/PIE/blob/master/specs/string.ml)
    for [String](http://caml.inria.fr/pub/docs/manual-ocaml/libref/String.html)
- **Loop Invariant Inference** (for C++ code)
  - 26 [HOLA Benchmarks](https://github.com/SaswatPadhi/PIE/tree/master/bm_oopsla)
  - 4 [String Benchmarks](https://github.com/SaswatPadhi/PIE/tree/master/bm_strings)

Additionally, we also test all 30 loop invariant inference benchmarks with only
Escher to show that verification of most of these benchmarks are not feasible with
simply a program synthesizer.

### Limiting & Monitoring Resource Usage

As described in the next section, each test script accepts a parameter `<cg>`
which is the name of a Linux `cgroup` ([ArchWiki](https://wiki.archlinux.org/index.php/Cgroups)).
A `cgroup` can limit and monitor the _total_ resource usage of a process with all
its sub-processes; by isolating them and running within a special environment.Our
scripts can optionally run and monitor our tools within a `cgroup`, if the user
specifies one.

Currently, we only monitor the memory usage of our tools. The script `PIE/mk_mem_cgroup`
creates a new `cgroup` with a user-specified name and limit on total memory usage.
Example invocation:
```html
~/Repos/PIE/mk_mem_cgroup "test_8gb" 8
```

This would create a new `cgroup` named <kbd>"test_8gb"</kbd> which can be used as a
`<cg>` parameter in the invocations described in the next section.
The `<cg>` parameter can always be empty <kbd>""</kbd>. Note that the quotes
are *necessary*, for your shell to even recognize that parameter.

**Note:** The virtual machine already creates the `test_8gb` cgroup on booting the
system.



## <i class="fa fa-fw fa-tasks" id="running-the-tests"></i> Running the Tests
-----------------------------------------------------------------------------

**Note:** This section assumes that the `llvm` directory (source code for LLVM and Clang projects)
is a sibling of `PIE` in the directory-tree. The test VM already has this setup; but if
you are manually testing and this does not hold, please change the relative paths in this
section accordingly.

### Precondition Inference Tests

**Note:** For testing this subsection, please `cd ~/Repos/PIE/specs`.

##### Testing _all_ preconditions for _all_ functions in _all_ modules with _all_ configurations
```bash
./test_all.sh [<cg>]
```
The brackets around <kbd>&lt;cg&gt;</kbd> indicate that this is an optional parameter. If
a `cgroup` name is provided, the `test_all.sh` script would test each instantiation of PIE
in a (clean) environment with the limits imposed by the `cgroup`; and report the memory usage.


The results presented in the paper were generated using:
```html
pie@pie-VirtualBox:~/Repos/PIE/specs$ ./test_all.sh "test_8gb"
```

The script prints the precondition, the postcondition, and running time for PIE
(with other details like module and function names). A successful run should
look something like:
```html
pie@pie-VirtualBox:~/Repos/PIE/specs$ ./test_all.sh



 ############ CG_SIZE = 2 ############

Scanning line 513 ... DONE


=== (0) List.length(l) ===
    [%] Inferring {exception thrown} [k = 1] (0f x 6400t) ...
precondition: false
postcondition: exception thrown
precondition: false
postcondition: exception thrown


real  0m0.010s
user  0m0.008s
sys 0m0.000s
Scanning line 513 ... DONE


=== (0) List.length(l) ===
    [%] Inferring {(res = 0)} [k = 1] (1f x 6400t) ...
precondition: (l = [])
postcondition: (res = 0)
precondition: (l = [])
postcondition: (res = 0)


real  0m0.020s
user  0m0.016s
sys 0m0.000s
Scanning line 513 ... DONE


=== (0) List.length(l) ===
Fatal error: exception Invalid_argument("Index past end of list")

real  0m0.002s
user  0m0.000s
sys 0m0.000s
Scanning line 513 ... DONE


=== (1) List.hd(l) ===
    [%] Inferring {exception thrown} [k = 1] (1f x 6400t) ...
precondition: (l = [])
postcondition: exception thrown
precondition: (l = [])
postcondition: exception thrown


real  0m0.018s
user  0m0.008s
sys 0m0.008s
Scanning line 513 ... DONE


=== (1) List.hd(l) ===
Fatal error: exception Invalid_argument("Index past end of list")

real  0m0.002s
user  0m0.000s
sys 0m0.000s
Scanning line 513 ... DONE


=== (2) List.tl(l) ===
    [%] Inferring {exception thrown} [k = 1] (1f x 6400t) ...
precondition: (l = [])
postcondition: exception thrown
precondition: (l = [])
postcondition: exception thrown


real  0m0.017s
user  0m0.012s
sys 0m0.000s

.
.
.
```

Couple of points to note:
- One might see a debug error about missing `RESULT` file, depending on whether or not it's
  the first time this script was run.
- The `Fatal error: exception Invalid_argument("Index past end of list")` is thrown when all
  postconditions for a particular function have been tested. I would suppress this at some point.

On running `test_all.sh` with a `cgroup`, the output should be similar but with memory usages
printed too (in MBs), like:

```html
pie@pie-VirtualBox:~/Repos/PIE/specs$ ./test_all.sh test_8gb



 ############ CG_SIZE = 2 ############

./test_all.sh: line 13: ../logs/test_8gb/6400/pie/2/specs/list/RESULT: No such file or directory
Scanning line 513 ... DONE


=== (0) List.length(l) ===
    [%] Inferring {exception thrown} [k = 1] (0f x 6400t) ...
precondition: false
postcondition: exception thrown
precondition: false
postcondition: exception thrown


real  0m0.034s
user  0m0.008s
sys 0m0.000s

[M]ax Memory Usage = 4


Scanning line 513 ... DONE


=== (0) List.length(l) ===
    [%] Inferring {(res = 0)} [k = 1] (1f x 6400t) ...
precondition: (l = [])
postcondition: (res = 0)
precondition: (l = [])
postcondition: (res = 0)


real  0m0.018s
user  0m0.016s
sys 0m0.000s

[M]ax Memory Usage = 6

.
.
.
```

<br>
##### Testing a specific function in a specific module
```bash
./test.sh <module> <func> <cg> <tests> <sz_conflicts>
```
- `<module>` The module's test file (one of the `.ml` files in
  [specs](https://github.com/SaswatPadhi/PIE/tree/master/specs))
- `<func>` = The index (starting from 0) of the function in the list of all
   tested functions at the end of the module's `.ml` file.
- `<cg>` = Empty string or a `cgroup` name
- `<tests>` = Maximum number of generated tests
- `<sz_conflicts>` = Maximum size of conflict groups passed to the synthesizer.

A successful run of `test.sh` should look like:
```bash
pie@pie-VirtualBox:~/Repos/PIE/specs$ ./test.sh batavltree.ml 5 test_8gb 6400 16
Scanning line 323 ... DONE


=== (5) BatAvlTree.right_branch(t) ===
    [%] Inferring {exception thrown} [k = 1] (1f x 6400t) ...
precondition: empty(t)
postcondition: exception thrown
precondition: empty(t)
postcondition: exception thrown


real  0m5.821s
user  0m5.048s
sys 0m0.336s

[M]ax Memory Usage = 9


Scanning line 323 ... DONE


=== (5) BatAvlTree.right_branch(t) ===
    [%] Inferring {empty(res)} [k = 1] (1f x 5101t) ...
precondition: empty(right(t))
postcondition: empty(res)
precondition: empty(right(t))
postcondition: empty(res)


real  0m5.802s
user  0m5.060s
sys 0m0.300s

[M]ax Memory Usage = 9


Scanning line 323 ... DONE


=== (5) BatAvlTree.right_branch(t) ===
Fatal error: exception Invalid_argument("Index past end of list")

real  0m5.725s
user  0m4.864s
sys 0m0.444s
```

### Loop Invariant Inference Benchmarks

**Note:** For testing this subsection, please `cd ~/Repos/llvm/build`.


##### Checking _all_ benchmarks with a specific PIE configuration
```bash
./check_all_with_config <tests> <tool> <cg> <sz_conflicts>
```
- `<tests>` = Maximum number of generated tests
- `<tool>` = PIE (`pie`) or just Escher (`escher`)
- `<cg>` = Empty string or a `cgroup` name
- `<sz_conflicts>` = Maximum size of conflict groups passed to the synthesizer.

A successful run of `check_all_with_config` should look something like:
```html
pie@pie-VirtualBox:~/Repos/llvm/build$ ./check_all_with_config 6400 pie "" all
[+] Checking /home/pie/Desktop/Repos/PIE/abducer/../bm_oopsla/00.cpp ...
*** Error in `bin/pinvgen': double free or corruption (out): 0x00007ffe36d1f5e0 ***
[+] Checking /home/pie/Desktop/Repos/PIE/abducer/../bm_oopsla/01.cpp ...
*** Error in `bin/pinvgen': double free or corruption (out): 0x00007ffd1f253da0 ***
[+] Checking /home/pie/Desktop/Repos/PIE/abducer/../bm_oopsla/02.cpp ...
.
.
.
```

The results presented in the paper were generated using:
```html
pie@pie-VirtualBox:~/Repos/llvm/build$ ./check_all_with_config 6400 pie "test_8gb" 16
```
for results with PIE, and using:
```html
pie@pie-VirtualBox:~/Repos/llvm/build$ ./check_all_with_config 6400 escher "test_8gb" all
```
for results with just Escher.

Couple of points to note:
- The memory errors `*** Error in 'bin/pinvgen': double free or corruption (out): 0x00007ffd1f253da0 ***`
  happens because our Clang tool does not cleanly release the AST. During the analysis, the AST nodes end
  up having multiple owners and thus are deleted by multiple destructors which is causing this issue. We
  are working on fixing it. This does not affect the correctness of the tool though.
- The output of `check_all_with_config` does not say a lot. But the results for each benchmark is stored
  in `PIE/logs/[<cg>/]<tests>/<tool>/<sz_conflicts>/<benchmark>/TOTAL.LOG`. Note that, depending on whether
  or not you are running within a `cgroup`, your path might have the `<cg>` parameter in it.  
  For example, after the execution shown above, the contents of `PIE/logs/6400/pie/all/00.cpp/TOTAL.LOG`
  looks like:
```html
 ==> 1027 final_tests.
​
(*) Checking loop invariant:
================================================================================
[#] Starting Loop Invariant Generation ...

   + Found guard in B4
     - guard : NON-DETERMINISTIC

   # Invariant Guess = true

   [V1] Verification query {pre} = true
     - Result = VALID

   [V2] Verification query {pos} = ((!true) | (!true) | (true & (x = y)))
     - Result = FAILED

   [Q1] Abduction query = ((!true) | (!true) | (true & (x = y)))
   [#] Simplified query: ((!true) | (!true) | (true & (x = y)))

    [%] Removing conflicts ...
    [%] Inferring {true} [k = 1] (0f x 1025t) ...
    [?] Verifying [k = 1] --- true
      [+] Added test ... [ 0, -1 ]

    [%] Removing conflicts ...  @2 @3
    [%] Inferring {true} [k = 1] (1f x 1026t) ...
    [?] Verifying [k = 1] --- (x = y)

     - Result = (x = y)

   # Invariant Guess = ((x = y) & true)

   [V3] Verification query {pre} = ((1 = 1) & true)
     - Result = VALID

   [V4] Verification query {pos} = ((!((x = y) & true)) | (!true) | (true & (x = y)))
     - Result = VALID

   [V5] Verification query {ind} = ((!((x = y) & true)) | (!true) | (((x + 1) = (y + 1)) & true))
     - Result = VALID
​
[###] Final invariant = ((x = y) & true) [###]
================================================================================
checker_exec.sh: line 1: 11077 Aborted                 (core dumped) bin/pinvgen -wpath /home/pie/Desktop/Repos/PIE/logs/6400/pie/all/00.cpp -abducer /home/pie/Desktop/Repos/PIE/abducer/abduce.sh -tool=pie -csize all --extra-arg=--std=c++11 /home/pie/Desktop/Repos/PIE/abducer/../bm_oopsla/00.cpp --
​
real  0m17.244s
user  0m15.988s
sys 0m0.296s
​
​
--- Processed 00.cpp ---
sat: 2
unsat: 5
unk: 0
escher: 1
```
- The last 4 lines indicated the number of calls to the constraint solver (with their results) and to the synthesizer.

<br>
##### Checking a specific benchmark
```bash
./checker <benchmark> <tests> <tool> <cg> <sz_conflicts>
```
- `<benchmark>` = The `.cpp` benchmark file (either from
  [bm_oopsla](https://github.com/SaswatPadhi/PIE/tree/master/bm_oopsla) or
  [bm_strings](https://github.com/SaswatPadhi/PIE/tree/master/bm_strings))
- `<tests>` = Maximum number of generated tests
- `<tool>` = PIE (`pie`) or just Escher (`escher`)
- `<cg>` = Empty string or a `cgroup` name
- `<sz_conflicts>` = Maximum size of conflict groups passed to the synthesizer.

A successful run of `checker` should look like:
```html
pie@pie-VirtualBox:~/Repos/llvm/build$ ./checker ../../PIE/bm_strings/cav2014d.cpp 6400 pie "test_8gb" all
(*) Collecting test data ... 256 / 256 ==> 6401 final_tests.

(*) Checking loop invariant:
================================================================================
[#] Starting Loop Invariant Generation ...

   + Found guard in B4
     - guard : NON-DETERMINISTIC

   # Invariant Guess = true

   [V1] Verification query {pre} = true
     - Result = VALID

   [V2] Verification query {pos} = ((!true) | (!true) | (true & #eql(#sub(r, 0, i), "a")))
     - Result = FAILED

   [Q1] Abduction query = ((!true) | (!true) | (true & #eql(#sub(r, 0, i), "a")))
   [#] Simplified query: ((!true) | (!true) | (true & #eql(#sub(r, 0, i), "a")))
    [?] Verifying [k = 1] --- true
      [+] Added test ... [ "", 0 ]
    [?] Verifying [k = 1] --- (#has(r, "a"))
close failed in file object destructor:
sys.excepthook is missing
lost sys.stderr
      [+] Added test ... [ "a", 0 ]
    [?] Verifying [k = 1] --- (1 = i)
      [+] Added test ... [ "A", 1 ]
    [?] Verifying [k = 1] --- (#has(r, "a")) & (1 = i)
      [+] Added test ... [ "Aa", 1 ]
    [?] Verifying [k = 1] --- (1 = i) & (#has("a", (#get(r, 0))))

     - Result = ((1 = i) & #has("a", #get(r, 0)))

   # Invariant Guess = (((1 = i) & #has("a", #get(r, 0))) & true)

   [V3] Verification query {pre} = (((1 = #len("a")) & #has("a", #get("a", 0))) & true)
     - Result = VALID

   [V4] Verification query {pos} = ((!(((1 = i) & #has("a", #get(r, 0))) & true)) | (!true) | (true & #eql(#sub(r, 0, i), "a")))
     - Result = VALID

   [V5] Verification query {ind} = ((!(((1 = i) & #has("a", #get(r, 0))) & true)) | (!true) | (((1 = i) & #has("a", #get(#cat(r, t), 0))) & true))
     - Result = VALID


[###] Final invariant = (((1 = i) & #has("a", #get(r, 0))) & true) [###]
================================================================================
*** Error in `bin/pinvgen': double free or corruption (out): 0x00007ffc0b6ca040 ***
checker_exec.sh: line 1: 13489 Aborted                 (core dumped) bin/pinvgen -wpath /home/pie/Desktop/Repos/PIE/logs/test_8gb/6400/pie/all/cav2014d.cpp -abducer /home/pie/Desktop/Repos/PIE/abducer/abduce.sh -tool=pie -csize all --extra-arg=--std=c++11 ../../PIE/bm_strings/cav2014d.cpp --

real  0m13.303s
user  0m11.876s
sys 0m0.400s


--- Processed cav2014d.cpp ---
sat: 5
unsat: 5
unk: 0
escher: 3

[$] OOM Count = 0
[$] MAX Usage = 172
```

Couple of points to note:
- Like `check_all_with_config`, `checker` also logs the result to `TOTAL.LOG`,
  but prints the same on screen too.
- The following errors:
    ```html
    close failed in file object destructor:
    sys.excepthook is missing
    lost sys.stderr
    ```
  are generated from Z3Str2, because of a [Python bug](http://bugs.python.org/issue11380).


## <i class="fa fa-fw fa-pencil-square-o" id="defining-custom-tests"></i> Defining Custom Tests
-----------------------------------------------------------------------------------------------

### Testing Precondition Inference

It might be easier to understand how the tests are instrumented, if we pick an example.
Let us examine `PIE/specs/batavltree.ml` which tests the functions in module `BatAvlTree`.
After including the standard OCaml libraries, a section of the file which defines the
precondition tests for a particular function (say `BatAvlTree.create`) looks like:
(additional comments have been inserted)

```html
(*** BatAvlTree.create ***)

(* PIE currently analyzes functions with single arguments *)
let avlcreate = fun (l,v,r) -> BatAvlTree.create l v r;;

(* The top-level function which runs the precondition tests *)
let createRes = fun ?(pind=(-1)) () ->
  (* For the humans *)
  let name = "create" in

  (* The function to be analyzed *)
  let f = avlcreate in

  (* The function to be analyzed *)
  let arguments = [ "l" ; "v" ; "r" ] in

  (* Random test generation, based on input type of f.
     These functions are defined in PIE/base/testGen.ml. *)
  let tests = iavltree_int_iavltree_tests () in

  (* A function to dump the input values (tests). *)
  let dumper = iavltree_int_iavltree_dumper in

  (* The type of the function input, in synthesizer's (Escher) type system.
     Escher operates on its own types. Functions in the Escher's language map a
     list of Escher-types (imagine a tuple); to an Escher-type.
     These functions are defined in PIE/base/escher_types.ml. *)
  let typ = [ TAVLTree ; TInt ; TAVLTree ] in

  (* Transformation function for mapping input values of f to Escher-types.
     Basically, we break the tuple to a list (why list? mentioned above), with
     each element of the list being in Escher-types.
     These functions are defined in PIE/base/escher_types.ml. *)
  let tfun = fun (l,v,r) -> [ of_avltree of_int l ; of_int v ; of_avltree of_int r ] in

  (* Type-based default features generation.
     The script PIE/base/preprocess.py reads these annotations and plugs in
     some simple features based on the types provided.
     Currently disabled. The Python script returns an empty list [] here. *)
  let def_features = (*PYF:t|T(l:R(1),v:1,r:R(1))*) in

  (* Additional user-defined features. *)
  let my_features = [] in

  (* Type-based default postconditions generation.
     The script PIE/base/preprocess.py reads these annotations and plugs in
     some simple postconditions based on the types provided.
     This can be empty [] though. Use might choose to provide their own
     postconditions. *)
  let def_postconditions = (*PYP:t|T(l:R(1),v:1,r:R(1))|R(1)*) in

  (* Additional user-defined postconditions. *)
  let my_postconditions = [] in

    (* Combine the stuff above and make required calls. *)
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                             ~arg_names:arguments f tests features
                             (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;
```

##### Custom postconditions

Users can define their own postconditions in the following format:
```html
let my_postconditions = [
  (* a postcondition is a pair of a binary boolean function and string *)
  (
    (* A boolean function that checks the postcondition, given input and output *)
    (fun input output_or_exception -> match output_or_exception with
        Bad _ -> ...                            (* postcondition for exceptions *)
        Ok output -> fancy_check(input, output) (* postcondition for normal output *)
    ),

    (* A human-readable comment on the postcondition *)
    "My fancy postcondition"
  );

  (fun i r -> match r with Bad _ | Ok o -> f(i,o) , "post_2")
]
```

##### Custom features

Similarly, features can be defined in the following format:
```html
let my_features = [
  (* a feature is a pair of a unary boolean function and string *)
  (
    (* A boolean function defined on input *)
    (fun input -> check_property_is_awesome(input)),

    (* A human-readable comment on the feature *)
    "My fancy feature"
  );

  (fun i -> is_awesome(i), "f2")
]
```

##### Custom types

PIE by itself, does not impose any restrictions on types. The restrictions arise
from:
- Requirements of the synthesizer
- For random test generation, the types should have a `_tests` function
- For input / output purposes, the types should have a `_dumper` function

Adding types to the synthesizer (Escher), is beyond the scope of this document.

But if the user's problem can be represented in the types supported by Escher,
then the user only needs to define `typ` and `tfun`.
(refer to the `BatAvlTree.create` example above)
- `typ` should be the type of the input (i.e. tests) when represented in Escher's
  types. As Escher-functions always accept their arguments as a List of Escher-types,
  `typ` must thus always be a List of Escher-types.
- `tfun` should be the function which can transform the tests to `tfun` type.

Defining `_tests` and `_dumper` function has been explained in `PIE/base/testGen.ml`
with sufficient examples.


### Testing Loop Invariant Inference

Currently our tool can handle single loop C++ programs over strings and integers.

##### Integers

Creating benchmarks for loop invariant inference is very simple. Let's start with
an example, [bm_oopsla/11.cpp](https://github.com/SaswatPadhi/PIE/blob/master/bm_oopsla/11.cpp):
```cpp
#include "bm_oopsla.h"      // For instrumentation functions and macros

int main(int argc, char* argv[]) {
  // RECORD macro defines the program state using the given variables, assuming
  // all integer variables. It also defines PRINT_VARS to print the state.
  RECORD(4, j, k, l, n);

  INIT_n(unknown);
  assume(n > 0);
  j = n; k = n; l = 0;

  while(j > l) {
    PRINT_VARS();           // Print the current program state
    j--;
    k--;
  }
  PRINT_VARS();             // Print the current program state

  assert(k >= l);
  return 0;
}
```
We only need to instrument the loop and the entry of the code:
1. `#include "bm_oopsla.h"`
2. Define the state using `RECORD` at the entry.
3. Any unknown variables at the entry, should be assigned as
    ```cpp
    INIT_myvar(my_unknown_function);
    ```
    instead of
    ```cpp
    myvar = my_unknown_function();
    ```
4. `PRINT_VARS()` at the loop head and just after the loop.

##### Strings

The string benchmarks are very similar to integer ones:
```cpp
#include "bm_strings.h"     // For instrumentation functions and macros

int main() {
  int i;
  string r, t;

  // INITIALIZE macro defines PRINT_VARS which prints the current program state.
  // The arguments are exactly like printf function.
  INITIALIZE("%d \t %s \t %s\n", i, t.c_str(), r.c_str());

  set(r, "a");
  i = len(r);

  while(unknown()) {
    PRINT_VARS();           // Print the current program state
    t = unknown_s(1);
    set(r, cat(r, t));
  }
  PRINT_VARS();             // Print the current program state

  assert(eql(sub(r, 0, i), "a"));
  return 0;
}
```
The key differences from the integer benchmarks being:
1. The header: `bm_strings.h`.
2. `RECORD` cannot be used any more, because it assumes all integer variables.
   Instead, we use a different macro: `INITIALIZE`.
3. `INITIALIZE` does _not_ declare variables unlike `RECORD`. It should thus be
   used after variables have been declared.
4. `INIT` is not defined. For string benchmarks, the counter example from solvers
   is directly added (instead of running the program rooted at the counter example).
   This would be fixed in next versions.
5. **Important**: For strings, we have defined in `bm_strings.h`, a subset of
   string operations which the constraint solvers can understand. These should be
   used instead of C++'s own string operations for the code to be analyzable by our tool.
   In the above example,
     - `set` is used instead of assignment.
     - `eql` is used to check equality, instead of `==` operator.
     - `sub` is used for substring, instead of `string.substr()`.
     - `cat` is used for concatenation, instead of `+` operator.
     - `len` is used for length, instead of `string.length`.

  Additionally, `has`, `get` and `ind` have been defined in `bm_strings.h`.


## <i class="fa fa-fw fa-cubes" id="modifying-and-rebuilding"></i> Modifying and Rebuilding
-------------------------------------------------------------------------------------------

No changes to PIE require recompilation / rebuilding. The OCaml code is rebuilt, but the
scripts take care of that; the user does not have to manually build anything.

Changes to the Clang tool (`pinvgen`) require rebuilding; but there are no tunable parameters
within the tool. All parameters to PIE are transparently passed through scripts, so PIE changes
do not affect the Clang tool.
