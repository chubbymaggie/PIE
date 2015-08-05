#require "qcheck"

#use "top_helper.ml"

open Generator

open SpecInfer

(* generate n random values with the given generator *)
let rec generate n ?(rand=Random.State.make_self_init()) gen =
  match n with
      0 -> []
    | _ -> (run gen rand)::(generate (n-1) ~rand:rand gen)

let int_gen = make_int (-3) 4
let posInt_gen = make_int (0) 6

(* generator for lists, given generator for element and an integer generator for length *)
let list_gen g (l: int gen) = fun rand ->
  let len = l rand in
  let res = ref [] in
  for i = 0 to len - 1 do res := ((g rand)::!res) done;
  !res

(* generator for pairs, given generators for each component *)
let pair_gen g1 g2 = app (app (pure (fun x y -> (x,y))) g1) g2

let intList_gen = list_gen int_gen posInt_gen
let intListList_gen = list_gen intList_gen posInt_gen
let intList_int_gen = pair_gen intList_gen int_gen
let int_intList_gen = pair_gen int_gen intList_gen
let intList_intList_gen = pair_gen intList_gen intList_gen
let int_int_List_gen = list_gen (pair_gen int_gen int_gen) posInt_gen

let test_size = 8192

let intList_tests = generate test_size intList_gen
let intListList_tests = generate test_size intListList_gen
let intList_int_tests = generate test_size intList_int_gen
let int_intList_tests = generate test_size int_intList_gen
let intList_intList_tests = generate test_size intList_intList_gen
let int_int_List_tests = generate test_size int_int_List_gen

(* #################### PROPERTIES  #################### *)

(*** List.length ***)

let lengthRes = fun () ->
let f = List.length in
let tests = intList_tests in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|I*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.hd ***)

let hdRes = fun () ->
let f = List.hd in
let tests = intList_tests in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|1*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.nth ***)

let lnth = fun (l,n) -> List.nth l n;;

let nthRes = fun () ->
let f = lnth in
let tests = intList_int_tests in
let typ = [ TList ; TInt ] in
let tfun = fun (l,n) -> [ of_list of_int l ; of_int n ] in
let def_features = (*PYF:l|T(l:L(1),n:I)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l:L(1),n:I)|1*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.mem ***)

let lmem = fun (m,l) -> List.mem m l;;

let memRes = fun () ->
let f = lmem in
let tests = int_intList_tests in
let typ = [ TInt ; TList ] in
let tfun = fun (m,l) -> [ of_int m ; of_list of_int l ] in
let def_features = (*PYF:l|T(m:1,l:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(m:1,l:L(1))|B*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(* #################### MUTATORS  #################### *)

(*** List.tl ***)

let tlRes = fun () ->
let f = List.tl in
let tests = intList_tests in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:l|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(1)|L(1)*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.append ***)

let lappend = fun (l0, l1) -> List.append l0 l1;;

let appendRes = fun () ->
let f = lappend in
let tests = intList_intList_tests in
let typ = [ TList ; TList ] in
let tfun = fun (l0, l1) -> [ of_list of_int l0 ; of_list of_int l1 ] in
let def_features = (*PYF:l|T(l0:L(1),l1:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(1))|L(1)*) in
let my_postconditions = [
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.length(l0) + List.length(l1)), "len(res) = len(l0)+len(l1)");
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) != List.length(l0) + List.length(l1)), "len(res) != len(l0)+len(l1)")
] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.combine ***)

let lcombine = fun (l1,l2) -> List.combine l1 l2;;

let combineRes = fun () ->
let f = lcombine in
let tests = intList_intList_tests in
let typ = [ TList ; TList ] in
let tfun = fun (l0, l1) -> [ of_list of_int l0 ; of_list of_int l1 ] in
let def_features = (*PYF:l|T(l0:L(1),l1:L(2))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(2))|L(T(x0:1,x1:2))*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.concat ***)

let concatRes = fun () ->
let f = List.concat in
let tests = intListList_tests in
let typ = [ TList ] in
let tfun = fun l -> [ of_list (of_list of_int) l ] in
let def_features = (*PYF:l|L(L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(L(1))|L(1)*) in
let my_postconditions = [
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) > List.fold_left (+) 0 (List.map List.length ls)), "len(res) > sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.fold_left (+) 0 (List.map List.length ls)), "len(res) = sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) < List.fold_left (+) 0 (List.map List.length ls)), "len(res) < sum(len(l0:lN))")
] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.flatten ***)

let flattenRes = fun () ->
let f = List.flatten in
let tests = intListList_tests in
let typ = [ TList ] in
let tfun = fun l -> [ of_list (of_list of_int) l ] in
let def_features = (*PYF:l|L(L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(L(1))|L(1)*) in
let my_postconditions = [
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) > List.fold_left (+) 0 (List.map List.length ls)), "len(res) > sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.fold_left (+) 0 (List.map List.length ls)), "len(res) = sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) < List.fold_left (+) 0 (List.map List.length ls)), "len(res) < sum(len(l0:lN))")
] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



let testConcatFlattenEquivalence = fun () ->
    concatRes() = flattenRes()
;;



(*** List.rev ***)

let revRes = fun () ->
let f = List.rev in
let tests = intList_tests in
let typ = [ TList ] in
let tfun = fun l -> [ of_list of_int l ] in
let def_features = (*PYF:a|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:a|L(1)|L(1)*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.rev_append ***)

let lrev_append = fun (l0, l1) -> List.rev_append l0 l1;;

let rev_appendRes = fun () ->
let f = lrev_append in
let tests = intList_intList_tests in
let typ = [ TList ; TList ] in
let tfun = fun (l0, l1) -> [ of_list of_int l0 ; of_list of_int l1 ] in
let def_features = (*PYF:l|T(l0:L(1),l1:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(1))|L(1)*) in
let my_postconditions = [
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.length(l0) + List.length(l1)), "len(res) = len(l0)+len(l1)");
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) != List.length(l0) + List.length(l1)), "len(res) != len(l0)+len(l1)")
] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;



(*** List.split ***)

let splitRes = fun () ->
let f = List.split in
let tests = int_int_List_tests in
let typ = [] in
let tfun = fun l -> [ ] in
let def_features = (*PYF:l|L(T(x0:1,x1:2))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(T(x0:1,x1:2))|T(r0:L(1),r1:L(2))*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;
