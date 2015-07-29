#use "pacSpec.ml";;



(*** List.append ***)

let lappend = fun (l0, l1) -> List.append l0 l1;;

let appendRes = fun () ->
let f = lappend in
let tests = (*PYT:1|T(l0:L(I), l1:L(I))*) in
let def_features = (*PYF:l|T(l0:L(1),l1:L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(l0:L(1),l1:L(1))|L(1)*) in
let my_postconditions = [
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.length(l0) + List.length(l1)), "len(res) = len(l0)+len(l1)");
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) != List.length(l0) + List.length(l1)), "len(res) != len(l0)+len(l1)")
] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;


(*
(*** List.combine ***)

let lcombine = fun (l1,l2) -> List.combine l1 l2;;

let combineRes = fun () ->
let f = lcombine in
let tests = [
    ([],[]);
    ([],["a"]);
    ([],["b";"c";"d"]);
    ([1;2;3],[]);
    ([5],[]);
    ([4],["p"]);
    ([0;0],["a";"b"]);
    ([1;2;3],["m";"n";"o"]);
] in
let def_features = (*PYF:l|T(L(1),L(2))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(L(1),L(2))|L(T(1,2))*) in
let my_postconditions = [] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;



(*** List.concat ***)

let concatRes = fun () ->
let f = List.concat in
let tests = [[];
             [[]];
             [[1]];
             [[];[];[]];
             [[];[1;2;3]];
             [[1;2];[3;4];[]];
             [[1;2];[];[3;4]];
             [[1];[];[2];[]];
             [[];[2;3];[]];
             [[1;2;3];[4;5;6]]
] in
let def_features = (*PYF:l|L(L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(L(1))|L(1)*) in
let my_postconditions = [
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) > List.fold_left (+) 0 (List.map List.length ls)), "len(res) > sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.fold_left (+) 0 (List.map List.length ls)), "len(res) = sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) < List.fold_left (+) 0 (List.map List.length ls)), "len(res) < sum(len(l0:lN))")
] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;



(*** List.flatten ***)

let flattenRes = fun () ->
let f = List.flatten in
let tests = [[];
             [[]];
             [[1]];
             [[];[];[]];
             [[];[1;2;3]];
             [[1;2];[3;4];[]];
             [[1;2];[];[3;4]];
             [[1];[];[2];[]];
             [[];[2;3];[]];
             [[1;2;3];[4;5;6]]
] in
let def_features = (*PYF:l|L(L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(L(1))|L(1)*) in
let my_postconditions = [
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) > List.fold_left (+) 0 (List.map List.length ls)), "len(res) > sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.fold_left (+) 0 (List.map List.length ls)), "len(res) = sum(len(l0:lN))");
    ((fun ls r -> match r with Bad _ -> false | Ok lr -> List.length(lr) < List.fold_left (+) 0 (List.map List.length ls)), "len(res) < sum(len(l0:lN))")
] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;



let testConcatFlattenEquivalence = fun () ->
    concatRes() = flattenRes()
;;



(*** List.rev ***)

let revRes = fun () ->
let f = List.rev in
let tests = [[];
             [1];
             [1;1];
             [1;2];
             [1;2;3];
             [1;2;1];
             [1;2;3;4];
             [1;2;2;1]] in
let def_features = (*PYF:a|L(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:a|L(1)|L(1)*) in
let my_postconditions = [] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;



(*** List.rev_append ***)

let lrev_append = fun (l0, l1) -> List.rev_append l0 l1;;

let rev_appendRes = fun () ->
let f = lrev_append in
let tests = [
    ([],[]);
    ([],[1]);
    ([1;2],[1;2]);
    ([],[1;2;3;4]);
    ([1],[1;2;3]);
    ([1;2;3;4;5],[1;2]);
    ([1;2;3;4],[1;2;9;8]);
    ([1;2],[3;4]);
    ([1;2;3],[]);
    ([2],[])
] in
let def_features = (*PYF:l|T(L(1),L(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|T(L(1),L(1))|L(1)*) in
let my_postconditions = [
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) = List.length(l0) + List.length(l1)), "len(res) = len(l0)+len(l1)");
    ((fun (l0,l1) r -> match r with Bad _ -> false | Ok lr -> List.length(lr) != List.length(l0) + List.length(l1)), "len(res) != len(l0)+len(l1)")
] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;



(*** List.split ***)

let splitRes = fun () ->
let f = List.split in
let tests = [
    [];
    [(1,"One")];
    [(0,"Zero")];
    [(10,"Ten");(-1,"Minus One");(100,"Hundred")];
    [(12,"Twelve");(16,"Sixteen");(-2,"Minus Two")]
] in
let def_features = (*PYF:l|L(T(1,2))*) in
let my_features = [] in
let def_postconditions = (*PYP:l|L(T(1,2))|T(L(1),L(2))*) in
let my_postconditions = [] in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;
*)
