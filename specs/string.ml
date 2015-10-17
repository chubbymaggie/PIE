#use "top_helper.ml"

(* INFERRING SPECS FOR STRING MODULE FUNCTIONS *)

(*** String.copy ***)

let scopy = String.copy

let scopyRes = fun () ->
let name = "scopy" in
let f = scopy in
let tests = string_tests () in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, string_dumper) ~record:name f tests features postconds trans
;;


(*** String.get ***)

let sget = (fun (s, i) -> String.get s i)

(* here we learn the precise conditions under which an exception is thrown:  i<0 or len(s) <= i
   however, we have no i<0 predicate, so it's expressed in a more complicated way:
   [Neg "i > 0"; Neg "len(s) > i"]; [Neg "i = 0"; Pos "len(s) = i"]
   they are equivalent given the fact that the length of a string is never negative.
*)
let sgetRes = fun () ->
let name = "sget" in
let f = sget in
let tests = string_int_tests () in
let typ = [ TString ; TInt ] in
let tfun = fun (s, i) -> [ of_string s ; of_int i ] in
let def_features = (*PYF:t|T(s:S,i:I)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I)|C*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, string_int_dumper) ~record:name f tests features postconds trans
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
let name = "ssub" in
let f = ssub in
let tests = string_int_int_tests () in
let typ = [ TString ; TInt ; TInt ] in
let tfun = fun (s, i1, i2) -> [ of_string s ; of_int i1 ; of_int i2 ] in
let def_features = (*PYF:t|T(s:S,i1:I,i2:I)*) in
let my_features = [] in
(* let def_postconditions =  (\*PYP:t|T(s:S,i1:I,i2:I)|S*\) in *)
let def_postconditions = [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, string_int_int_dumper) ~record:name f tests features postconds trans
;;


(*** String.make ***)

let smake = (fun (i,c) -> String.make i c)

let smakeRes = fun () ->
let name = "smake" in
let f = smake in
let tests = int_char_tests () in
let typ = [ TInt ; TChar ] in
let tfun = fun (i, c) -> [ of_int i ; of_char c ] in
let def_features = (*PYF:t|T(i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(i:I,c:C)|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, int_char_dumper) ~record:name f tests features postconds trans
;;


(*** String.index ***)

let sindex = (fun (s,c) -> String.index s c)

let sindexRes = fun () ->
let name = "sindex" in
let f = sindex in
let tests = string_char_tests () in
let typ = [ TString ; TChar ] in
let tfun = fun (s, c) -> [ of_string s ; of_char c ] in
let def_features = (*PYF:t|T(s:S,c:C)*) in
let my_features = [] in
(* let def_postconditions = (\*PYP:t|T(s:S,c:C)|I*\) in *)
let def_postconditions = [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, string_char_dumper) ~record:name f tests features postconds trans
;;


(*** String.indexFrom ***)

let sindexFrom = (fun (s,i,c) -> String.index_from s i c)

let sindexFromRes = fun () ->
let name = "sindexFrom" in
let f = sindexFrom in
let tests = string_int_char_tests () in
let typ = [ TString ; TInt; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
(* let def_postconditions = (\*PYP:t|T(s:S,i:I,c:C)|I*\) in *)
let def_postconditions = [((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")] in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, string_int_char_dumper) ~record:name f tests features postconds trans
;;


(*** String.concat ***)

let sconcat = (fun (s,sl) -> String.concat s sl)

let sconcatRes = fun () ->
let name = "sconcat" in
let f = sconcat in
let tests = string_stringList_tests () in
let typ = [ TString ; TList ] in
let tfun = fun (s, sl) -> [ of_string s ; of_list of_string sl ] in
let def_features = (*PYF:t|T(s:S,sl:L(S))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,sl:L(S))|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, string_stringList_dumper) ~record:name f tests features postconds trans
;;

