
(* for generating random tests *)
#require "qcheck";;
open Generator

open SpecInfer

let genOne ?(rand=Random.State.make_self_init()) gen = run gen rand
  
(* generate n random values with the given generator *)  
let rec generate n ?(rand=Random.State.make_self_init()) gen =
  match n with
      0 -> []
    | _ ->
	(run gen rand)::(generate (n-1) ~rand:rand gen)

let smallintGen = make_int (-2) 3	  
	  
(* generator for alphanumeric strings of size up to 4 *)
let stringGen =
  string (make_int 0 4)
    (choose [lowercase; uppercase; select ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9']])
let strtests = generate 10000 stringGen

(* generator for random tuples of the above strings and small ints *)
let stringintGen = app (app (pure (fun x y -> (x,y))) stringGen) smallintGen
let stringinttests = generate 10000 stringintGen  


(* generator for random tuples of the above strings and two small ints *)
let stringintintGen = app (app (app (pure (fun x y z -> (x,y,z))) stringGen) smallintGen) smallintGen
let stringintinttests = generate 10000 stringintintGen  

(*** String.copy ***)

let scopy = String.copy

let scopyRes = fun () ->
let f = scopy in
let tests = strtests in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = []
  in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;


(*** String.get ***)

let sget = (fun (s, i) -> String.get s i)

(* here we learn the precise conditions under which an exception is thrown:  i<0 or len(s) <= i
   however, we have no i<0 predicate, so it's expressed in a more complicated way:
   [Neg "i > 0"; Neg "len(s) > i"]; [Neg "i = 0"; Pos "len(s) = i"]
   they are equivalent given the fact that the length of a string is never negative.
*)
let sgetRes = fun () ->
let f = sget in
let tests = stringinttests in
let def_features = (*PYF:t|T(s:S,i:I)*) in
let my_features = [] in
  (* currently no Python postcondition generation for characters, I believe *)
let def_postconditions =
  [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = []
  in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;


(*** String.sub ***)

let ssub = (fun (s, i1, i2) -> String.sub s i1 i2)

(* the ideal precondition for when an exception is thrown:
   0 <= i1 && 0 <= i2 && (i1 + i2) <= length(s)
   if we can do it, this one is nice for several reasons:
     - it's unclear from the type whether i2 is the end index or the length
     - even if that's known, the boundary conditions might be unclear
       (e.g., you are allowed to ask for (String.sub "hello" 5 0))
*)
  
let ssubRes = fun () ->
let f = ssub in
let tests = stringintinttests in
let def_features = (*PYF:t|T(s:S,i1:I,i2:I)*) in
let my_features = [] in
  (* currently no Python postcondition generation for characters, I believe *)
let def_postconditions =
  [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = []
  in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
        (List.filter (fun (pc, grp) -> grp != [])
                     (List.map (fun postcond -> (postcond, missingFeatures f tests features postcond)) postconds),
         (pacLearnSpec f tests features postconds))
;;
