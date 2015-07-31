#use "top_helper.ml"


open SpecInfer


(*** List.append ***)

let lappend = fun (l0, l1) -> List.append l0 l1;;

let appendRes = fun () ->
let f = lappend in
let tests = (*PYT:4096|T(l0:L(I),l1:L(I))*) in
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
let tests = (*PYT:4096|T(l0:L(I),l1:L(I))*) in
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
let tests = (*PYT:4096|L(L(I))*) in
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
let tests = (*PYT:4096|L(L(I))*) in
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
let tests = (*PYT:4096|L(I)*) in
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
let tests = (*PYT:4096|T(l0:L(I),l1:L(I))*) in
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
let tests = (*PYT:4096|L(T(x0:I,x1:I))*) in
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
