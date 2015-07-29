open SpecInfer

(*** List.append ***)

let lappend = fun (l0, l1) -> List.append l0 l1;;

let appendRes = fun () ->
let f = lappend in
let tests = (*PYT:1024|T(l0:L(I), l1:L(I))*) in
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
