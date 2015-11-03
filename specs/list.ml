#use "top_helper.ml"

(* #################### PROPERTIES  #################### *)

(*** List.length ***)

let lengthRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.hd ***)

let hdRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.nth ***)

let lnth = fun (l,n) -> List.nth l n;;

let nthRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.mem ***)

let lmem = fun (m,l) -> List.mem m l;;

let memRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(* #################### MUTATORS  #################### *)



(*** List.rev ***)

let revRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.tl ***)

let tlRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.append ***)

let lappend = fun (l0, l1) -> List.append l0 l1;;

let appendRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.combine ***)

let lcombine = fun (l1,l2) -> List.combine l1 l2;;

let combineRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.concat ***)

let concatRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.flatten ***)

let flattenRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



let testConcatFlattenEquivalence = fun () ->
    concatRes() = flattenRes()
;;



(*** List.rev_append ***)

let lrev_append = fun (l0, l1) -> List.rev_append l0 l1;;

let rev_appendRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.split ***)

let splitRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



(*** List.assoc ***)

let lassoc = fun (a,l) -> List.assoc a l;;

let assocRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



let lmem_assoc = fun (a,l) -> List.mem_assoc a l;;

let mem_assocRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;



let lremove_assoc = fun (a,l) -> List.remove_assoc a l;;

let remove_assocRes = fun () ->
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
                           ~arg_names:arguments f tests features postconds trans
;;
