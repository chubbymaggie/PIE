open Batteries
open QCheck.Arbitrary
open TestGen
open Escher_types
open Escher_core
open Escher_components
open Escher_synth
open Pie


(*** List.length ***)

let lengthRes = fun ?(pind=(-1)) () ->
let name = "length" in
let f = List.length in
let arguments = [ "l" ] in
let tests = intList_tests () in
let dumper = intList_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|I*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.hd ***)

let hdRes = fun ?(pind=(-1)) () ->
let name = "hd" in
let f = List.hd in
let arguments = [ "l" ] in
let tests = intList_tests () in
let dumper = intList_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|1*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.nth ***)

let lnth = fun (l,n) -> List.nth l n;;

let nthRes = fun ?(pind=(-1)) () ->
let name = "nth" in
let f = lnth in
let arguments = [ "l" ; "n" ] in
let tests = intList_int_tests () in
let dumper = intList_int_dumper in
let typ = [ TList ; TInt ] in
let tfun = fun (l,n) -> [ of_list of_int l ; of_int n ] in
let def_features = (*PYF:l|T(l:L(1),n:I)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l:L(1),n:I)|1*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.mem ***)

let lmem = fun (m,l) -> List.mem m l;;

let memRes = fun ?(pind=(-1)) () ->
let name = "mem" in
let f = lmem in
let arguments = [ "m" ; "l" ] in
let tests = int_intList_tests () in
let dumper = int_intList_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (m,l) -> [ of_int m ; of_list of_int l ] in
let def_features = (*PYF:l|T(m:1,l:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(m:1,l:L(1))|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.memq ***)

let lmemq = fun (m,l) -> List.memq m l;;

let memqRes = fun ?(pind=(-1)) () ->
let name = "memq" in
let f = lmemq in
let arguments = [ "m" ; "l" ] in
let tests = int_intList_tests () in
let dumper = int_intList_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (m,l) -> [ of_int m ; of_list of_int l ] in
let def_features = (*PYF:l|T(m:1,l:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(m:1,l:L(1))|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.rev ***)

let revRes = fun ?(pind=(-1)) () ->
let name = "rev" in
let f = List.rev in
let arguments = [ "l" ] in
let tests = intList_tests () in
let dumper = intList_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|L(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.tl ***)

let tlRes = fun ?(pind=(-1)) () ->
let name = "tl" in
let f = List.tl in
let arguments = [ "l" ] in
let tests = intList_tests () in
let dumper = intList_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|L(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.append ***)

let lappend = fun (l0, l1) -> List.append l0 l1;;

let appendRes = fun ?(pind=(-1)) () ->
let name = "append" in
let f = lappend in
let arguments = [ "l0" ; "l1" ] in
let tests = intList_intList_tests () in
let dumper = intList_intList_dumper in
let typ = [ TList ; TList ] in
let tfun = fun (l0, l1) -> [ of_list of_int l0 ; of_list of_int l1 ] in
let def_features = (*PYF:l|T(l0:L(1),l1:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(1))|L(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.combine ***)

let lcombine = fun (l1,l2) -> List.combine l1 l2;;

let combineRes = fun ?(pind=(-1)) () ->
let name = "combine" in
let f = lcombine in
let arguments = [ "l0" ; "l1" ] in
let tests = intList_intList_tests () in
let dumper = intList_intList_dumper in
let typ = [ TList ; TList ] in
let tfun = fun (l0, l1) -> [ of_list of_int l0 ; of_list of_int l1 ] in
let def_features = (*PYF:l|T(l0:L(1),l1:L(2))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(2))|L(T(x0:1,x1:2))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.concat ***)

let concatRes = fun ?(pind=(-1)) () ->
let name = "concat" in
let f = List.concat in
let arguments = [ "l" ] in
let tests = intListList_tests () in
let dumper = intListList_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list (of_list of_int) l ] in
let def_features = (*PYF:l|L(L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(L(1))|L(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.flatten ***)

let flattenRes = fun ?(pind=(-1)) () ->
let name = "flatten" in
let f = List.flatten in
let arguments = [ "l" ] in
let tests = intListList_tests () in
let dumper = intListList_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list (of_list of_int) l ] in
let def_features = (*PYF:l|L(L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(L(1))|L(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let testConcatFlattenEquivalence = fun ?(pind=(-1)) () ->
    concatRes() = flattenRes()
;;



(*** List.rev_append ***)

let lrev_append = fun (l0, l1) -> List.rev_append l0 l1;;

let rev_appendRes = fun ?(pind=(-1)) () ->
let name = "rev_append" in
let f = lrev_append in
let arguments = [ "l0" ; "l1" ] in
let tests = intList_intList_tests () in
let dumper = intList_intList_dumper in
let typ = [ TList ; TList ] in
let tfun = fun (l0, l1) -> [ of_list of_int l0 ; of_list of_int l1 ] in
let def_features = (*PYF:l|T(l0:L(1),l1:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(1))|L(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.split ***)

let splitRes = fun ?(pind=(-1)) () ->
let name = "split" in
let f = List.split in
let arguments = [ "l" ] in
let tests = int_int_List_tests () in
let dumper = int_int_List_dumper in
let typ = [ TList ] in
let tfun = fun l -> [ of_list (fun (x,y) -> VList [VInt x ; VInt y]) l ] in
let def_features = (*PYF:l|L(T(x0:1,x1:2))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(T(x0:1,x1:2))|T(r0:L(1),r1:L(2))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.assoc ***)

let lassoc = fun (a,l) -> List.assoc a l;;

let assocRes = fun ?(pind=(-1)) () ->
let name = "assoc" in
let f = lassoc in
let arguments = [ "a" ; "l" ] in
let tests = int__int_int_List_tests () in
let dumper = int__int_int_List_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (a,l) -> [ of_int a ; of_list (fun (x,y) -> VList [ of_int x ; of_int y ]) l ] in
let def_features = (*PYF:l|T(a:1,l:L(T(x:1,y:2)))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(a:1,l:L(T(x:1,y:2)))|2*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let lmem_assoc = fun (a,l) -> List.mem_assoc a l;;

let mem_assocRes = fun ?(pind=(-1)) () ->
let name = "mem_assoc" in
let f = lmem_assoc in
let arguments = [ "a" ; "l" ] in
let tests = int__int_int_List_tests () in
let dumper = int__int_int_List_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (a,l) -> [ of_int a ; of_list (fun (x,y) -> VList [ of_int x ; of_int y ]) l ] in
let def_features = (*PYF:l|T(a:1,l:L(T(x:1,y:2)))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(a:1,l:L(T(x:1,y:2)))|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let lremove_assoc = fun (a,l) -> List.remove_assoc a l;;

let remove_assocRes = fun ?(pind=(-1)) () ->
let name = "remove_assoc" in
let f = lremove_assoc in
let arguments = [ "a" ; "l" ] in
let tests = int__int_int_List_tests () in
let dumper = int__int_int_List_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (a,l) -> [ of_int a ; of_list (fun (x,y) -> VList [ of_int x ; of_int y ]) l ] in
let def_features = (*PYF:l|T(a:1,l:L(T(x:1,y:2)))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(a:1,l:L(T(x:1,y:2)))|L(T(p:1,q:2))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** List.assq ***)

let lassq = fun (a,l) -> List.assq a l;;

let assqRes = fun ?(pind=(-1)) () ->
let name = "assq" in
let f = lassq in
let arguments = [ "a" ; "l" ] in
let tests = int__int_int_List_tests () in
let dumper = int__int_int_List_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (a,l) -> [ of_int a ; of_list (fun (x,y) -> VList [ of_int x ; of_int y ]) l ] in
let def_features = (*PYF:l|T(a:1,l:L(T(x:1,y:2)))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(a:1,l:L(T(x:1,y:2)))|2*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let lmem_assq = fun (a,l) -> List.mem_assq a l;;

let mem_assqRes = fun ?(pind=(-1)) () ->
let name = "mem_assq" in
let f = lmem_assq in
let arguments = [ "a" ; "l" ] in
let tests = int__int_int_List_tests () in
let dumper = int__int_int_List_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (a,l) -> [ of_int a ; of_list (fun (x,y) -> VList [ of_int x ; of_int y ]) l ] in
let def_features = (*PYF:l|T(a:1,l:L(T(x:1,y:2)))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(a:1,l:L(T(x:1,y:2)))|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let lremove_assq = fun (a,l) -> List.remove_assq a l;;

let remove_assqRes = fun ?(pind=(-1)) () ->
let name = "remove_assq" in
let f = lremove_assq in
let arguments = [ "a" ; "l" ] in
let tests = int__int_int_List_tests () in
let dumper = int__int_int_List_dumper in
let typ = [ TInt ; TList ] in
let tfun = fun (a,l) -> [ of_int a ; of_list (fun (x,y) -> VList [ of_int x ; of_int y ]) l ] in
let def_features = (*PYF:l|T(a:1,l:L(T(x:1,y:2)))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(a:1,l:L(T(x:1,y:2)))|L(T(p:1,q:2))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let () =
    test_size := __TEST_SIZE__ ;
    max_conflict_set_size := __MAX_CONFLICT_SET_SIZE__ ;
    let run = (fun ((s, f) : (string * (?pind:int -> unit -> 'a))) ->
                  output_string stderr ("\n\n=== (" ^ (string_of_int __FUNCTION_INDEX__) ^ ") " ^ s ^ " ===\n") ;
                  print_specs stderr (f ~pind:__POST_INDEX__ ())) in
        run (List.nth [ ("List.length(l)", lengthRes) ;
                        ("List.hd(l)", hdRes) ;
                        ("List.tl(l)", tlRes) ;
                        ("List.nth(l, n)", nthRes) ;
                        ("List.rev(l)", revRes) ;
                        ("List.append(l0, l1)", appendRes) ;
                        ("List.rev_append(l0, l1)", rev_appendRes) ;
                        ("List.concat(l)", concatRes) ;
                        ("List.flatten(l)", flattenRes) ;
                        ("List.mem(m, l)", memRes) ;
                        ("List.memq(m, l)", memqRes) ;
                        ("List.split(l)", splitRes) ;
                        ("List.combine(l0, l1)", combineRes);
                        ("List.assoc(a, l)", assocRes) ;
                        ("List.assq(a, l)", assqRes) ;
                        ("List.mem_assoc(a, l)", mem_assocRes) ;
                        ("List.mem_assq(a, l)", mem_assqRes) ;
                        ("List.remove_assoc(a, l)", remove_assocRes) ;
                        ("List.remove_assq(a, l)", remove_assqRes) ] __FUNCTION_INDEX__)
