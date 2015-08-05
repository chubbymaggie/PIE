(* for generating random tests *)
#require "qcheck"

#use "top_helper.ml"

open Generator

open SpecInfer

(* SOME GENERATORS FOR RANDOM TESTS *)  
  
let genOne ?(rand=Random.State.make_self_init()) gen = run gen rand

(* generate n random values with the given generator *)
let rec generate n ?(rand=Random.State.make_self_init()) gen =
  match n with
      0 -> []
    | _ -> (run gen rand)::(generate (n-1) ~rand:rand gen)

let smallintGen = make_int (-3) 4

(* let charGen = (choose [lowercase; uppercase; select ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9']]) *)
let charGen = lowercase

(* generator for alphanumeric strings of size up to 4 *)
let stringGen = string (make_int 0 12) charGen

let strtests = generate 10000 stringGen

(* generator for pairs, given generators for each component *)
let genPair g1 g2 = app (app (pure (fun x y -> (x,y))) g1) g2

(* generator for triples, given generators for each component *)
let genTriple g1 g2 g3 = app (app (app (pure (fun x y z -> (x,y,z))) g1) g2) g3

(* generator for quads, given generators for each component *)
let genQuad g1 g2 g3 g4 = app (app (app (app (pure (fun x y z w -> (x,y,z,w))) g1) g2) g3) g4

(* generator for quints, given generators for each component *)
let genQuint g1 g2 g3 g4 g5 = app (app (app (app (app (pure (fun x y z w v -> (x,y,z,w,v))) g1) g2) g3) g4) g5

(* generator for random tuples of the above strings and small ints *)
let stringintGen = genPair stringGen smallintGen
let stringinttests = generate 10000 stringintGen


(* generator for random tuples of the above strings and two small ints *)
let stringintintGen = genTriple stringGen smallintGen smallintGen
let stringintinttests = generate 10000 stringintintGen

(* generator for random tuples of small ints and characters *)
let intcharGen = genPair smallintGen charGen
let intchartests = generate 10000 intcharGen


(* INFERRING SPECS FOR STRING MODULE FUNCTIONS *)  

(*** String.copy ***)

let scopy = String.copy

let scopyRes = fun () ->
let f = scopy in
let tests = strtests in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
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
let typ = [ TString ; TInt ] in
let tfun = fun (s, i) -> [ of_string s ; of_int i ] in
let def_features = (*PYF:t|T(s:S,i:I)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I)|C*) in
let my_postconditions = []
  in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;


(*** String.sub ***)

let ssub = (fun (s, i1, i2) -> String.sub s i1 i2)

(* the ideal precondition for when an exception is thrown:
   i1 < 0 || i2 < 0 || (i1 + i2) > length(s)
   if we can do it, this one is nice for several reasons:
     - it's unclear from the type whether i2 is the end index or the length
     - even if that's known, the boundary conditions might be unclear
       (e.g., you are allowed to ask for (String.sub "hello" 5 0))
*)

(* currently we get None for the above precondition.
   however, within a small scope we can get spurious results for other postconditions,
   including "terminates normally".  by moving to larger scopes -- in particular I increased
   the range of integers and increased the sizes of strings -- we properly get None for these.
   and we get one correct spec:
   (Some [[Pos "i2 = 0"]; [Neg "i1 < i2"]; [Neg "len(s) < i1"]],
    "len(res) = 0");
   but we still get one spurious spec with the current settings:
   (Some
     [[Pos "i2 % 2 = 0"]; [Neg "i1 < 0"]; [Pos "i2 = 0"; Neg "i1 > i2"];
      [Neg "len(s) < i1"]; [Neg "len(s) < i2"];
      [Pos "i1 = 0"; Neg "len(s) = i2"];
      [Pos "len(s) % 2 = 0"; Pos "i2 = 0"; Pos "i1 < i2"]],
    "len(res) % 2 = 0")]

   we can identify spurious ones as having lots of clauses.  the question is what to do then?
   - increase the scope of tests to try to get conflicts?
   - remove some features to try to get conflicts?
*)

  
let ssubRes = fun () ->
let f = ssub in
let tests = stringintinttests in
let typ = [ TString ; TInt ; TInt ] in
let tfun = fun (s, i1, i2) -> [ of_string s ; of_int i1 ; of_int i2 ] in
let def_features = (*PYF:t|T(s:S,i1:I,i2:I)*) in
let my_features = [] in
(* let def_postconditions =  (\*PYP:t|T(s:S,i1:I,i2:I)|S*\) in *)
let def_postconditions = [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = []
in
let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;


(*** String.make ***)

let smake = (fun (i,c) -> String.make i c)

let smakeRes = fun () ->
let f = smake in
let tests = intchartests in
let typ = [ TInt ; TChar ] in
let tfun = fun (i, c) -> [ of_int i ; of_char c ] in
let def_features = (*PYF:t|T(i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(i:I,c:C)|S*) in
let my_postconditions = []
  in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;


(*** String.index ***)

let sindex = (fun (s,c) -> String.index s c)

let sindexRes = fun () ->
let f = sindex in
let tests = generate 10000 (genPair stringGen charGen) in
let typ = [ TString ; TChar ] in
let tfun = fun (s, c) -> [ of_string s ; of_char c ] in
let def_features = (*PYF:t|T(s:S,c:C)*) in
let my_features = [] in
(* let def_postconditions = (\*PYP:t|T(s:S,c:C)|I*\) in *)
let def_postconditions = [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = []
  in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;


(*** String.indexFrom ***)

let sindexFrom = (fun (s,i,c) -> String.index_from s i c)

let sindexFromRes = fun () ->
let f = sindexFrom in
let tests = generate 10000 (genTriple stringGen smallintGen charGen) in
let typ = [ TString ; TInt; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
(* let def_postconditions = (\*PYP:t|T(s:S,i:I,c:C)|I*\) in *)
let def_postconditions = [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = []
  in
    let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
      resolveAndPacLearnSpec f tests features postconds trans []
;;


		     
