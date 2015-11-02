#use "top_helper.ml"

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
let arguments = [ "s" ; "i" ] in
let tests = string_int_tests () in
let dumper = string_int_dumper in
let typ = [ TString ; TInt ] in
let tfun = fun (s, i) -> [ of_string s ; of_int i ] in
let def_features = (*PYF:t|T(s:S,i:I)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I)|C*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.set ***)

let sset = (fun (s, i, c) -> let sc = String.copy s in String.set sc i c ; sc)

let ssetRes = fun () ->
let name = "sset" in
let f = sset in
let arguments = [ "s" ; "i" ; "c" ] in
let tests = string_int_char_tests () in
let dumper = string_int_char_dumper in
let typ = [ TString ; TInt ; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i ; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I,c:C)|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.create ***)

let screateRes = fun () ->
let name = "screate" in
let f = String.create in
let arguments = [ "i" ] in
let tests = int_tests () in
let dumper = int_dumper in
let typ = [ TInt ] in
let tfun = fun i -> [ of_int i ] in
let def_features = (*PYF:i|I*) in
let my_features = [] in
let def_postconditions = (*PYP:i|I|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.make ***)

let smake = fun (i,c) -> String.make i c;;

let smakeRes = fun () ->
let name = "smake" in
let f = smake in
let arguments = [ "i" ; "c" ] in
let tests = int_char_tests () in
let dumper = int_char_dumper in
let typ = [ TInt ; TChar ] in
let tfun = fun (i,c) -> [ of_int i ; of_char c ] in
let def_features = (*PYF:a|T(i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:a|T(i:I,c:C)|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.copy ***)

let scopyRes = fun () ->
let name = "scopy" in
let f = String.copy in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
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
let arguments = [ "s" ; "i1" ; "i2" ] in
let tests = string_int_int_tests () in
let dumper = string_int_int_dumper in
let typ = [ TString ; TInt ; TInt ] in
let tfun = fun (s, i1, i2) -> [ of_string s ; of_int i1 ; of_int i2 ] in
let def_features = (*PYF:t|T(s:S,i1:I,i2:I)*) in
let my_features = [] in
let def_postconditions =  (*PYP:t|T(s:S,i1:I,i2:I)|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.fill ***)

let sfill = (fun (s0,i0,i1,c) -> let sc = String.copy s0 in String.fill s0 i0 i1 c ; sc)

let sfillRes = fun () ->
let name = "sfill" in
let f = sfill in
let arguments = [ "s0" ; "i0" ; "i1" ; "c" ] in
let tests = string_int_int_char_tests () in
let dumper = string_int_int_char_dumper in
let typ = [ TString ; TInt ; TInt ; TChar ] in
let tfun = fun (s0,i0,i1,c) -> [ of_string s0 ; of_int i0 ; of_int i1 ; of_char c ] in
let def_features = (*PYF:a|T(s0:S,i0:I,i1:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s0:S,i0:I,i1:I,c:C)|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.blit ***)

let sblit = (fun (s0,i0,s1,i1,il) -> let sc = String.copy s0 in String.blit s0 i0 s1 i1 il ; sc)

let sblitRes = fun () ->
let name = "sblit" in
let f = sblit in
let arguments = [ "s0" ; "i0" ; "s1" ; "i1" ; "il" ] in
let tests = string_int_string_int_int_tests () in
let dumper = string_int_string_int_int_dumper in
let typ = [ TString ; TInt ; TString ; TInt ; TInt ] in
let tfun = fun (s0,i0,s1,i1,il) -> [ of_string s0 ; of_int i0 ; of_string s1 ; of_int i1 ; of_int il ] in
let def_features = (*PYF:a|T(s0:S,i0:I,s1:S,i1:I,il:I)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s0:S,i0:I,s1:S,i1:I,il:I)|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.concat ***)

let sconcat = (fun (s,sl) -> String.concat s sl)

let sconcatRes = fun () ->
let name = "sconcat" in
let f = sconcat in
let arguments = [ "s" ; "sl" ] in
let tests = string_stringList_tests () in
let dumper = string_stringList_dumper in
let typ = [ TString ; TList ] in
let tfun = fun (s, sl) -> [ of_string s ; of_list of_string sl ] in
let def_features = (*PYF:t|T(s:S,sl:L(S))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,sl:L(S))|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.trim ***)

let strimRes = fun () ->
let name = "strim" in
let f = String.trim in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.escaped ***)

let sescapedRes = fun () ->
let name = "sescaped" in
let f = String.escaped in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.index ***)

let sindex = (fun (s,c) -> String.index s c)

let sindexRes = fun () ->
let name = "sindex" in
let f = sindex in
let arguments = [ "s" ; "c" ] in
let tests = string_char_tests () in
let dumper = string_char_dumper in
let typ = [ TString ; TChar ] in
let tfun = fun (s, c) -> [ of_string s ; of_char c ] in
let def_features = (*PYF:t|T(s:S,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,c:C)|I*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.rindex ***)

let srindex = (fun (s,c) -> String.rindex s c)

let srindexRes = fun () ->
let name = "srindex" in
let f = srindex in
let arguments = [ "s" ; "c" ] in
let tests = string_char_tests () in
let dumper = string_char_dumper in
let typ = [ TString ; TChar ] in
let tfun = fun (s, c) -> [ of_string s ; of_char c ] in
let def_features = (*PYF:t|T(s:S,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,c:C)|I*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.index_from ***)

let sindex_from = (fun (s,i,c) -> String.index_from s i c)

let sindex_fromRes = fun () ->
let name = "sindex_from" in
let f = sindex_from in
let arguments = [ "s" ; "i" ; "c" ] in
let tests = string_int_char_tests () in
let dumper = string_int_char_dumper in
let typ = [ TString ; TInt; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I,c:C)|I*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.rindex_from ***)

let srindex_from = (fun (s,i,c) -> String.rindex_from s i c)

let srindex_fromRes = fun () ->
let name = "srindex_from" in
let f = srindex_from in
let arguments = [ "s" ; "i" ; "c" ] in
let tests = string_int_char_tests () in
let dumper = string_int_char_dumper in
let typ = [ TString ; TInt; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I,c:C)|I*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.contains ***)

let scontains = (fun (s,c) -> String.contains s c)

let scontainsRes = fun () ->
let name = "scontains" in
let f = scontains in
let arguments = [ "s" ; "c" ] in
let tests = string_char_tests () in
let dumper = string_char_dumper in
let typ = [ TString ; TChar ] in
let tfun = fun (s, c) -> [ of_string s ; of_char c ] in
let def_features = (*PYF:t|T(s:S,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,c:C)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.contains_from ***)

let scontains_from = (fun (s,i,c) -> String.contains_from s i c)

let scontains_fromRes = fun () ->
let name = "scontains_from" in
let f = scontains_from in
let arguments = [ "s" ; "i" ; "c" ] in
let tests = string_int_char_tests () in
let dumper = string_int_char_dumper in
let typ = [ TString ; TInt; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I,c:C)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.rcontains_from ***)

let srcontains_from = (fun (s,i,c) -> String.rcontains_from s i c)

let srcontains_fromRes = fun () ->
let name = "srcontains_from" in
let f = srcontains_from in
let arguments = [ "s" ; "i" ; "c" ] in
let tests = string_int_char_tests () in
let dumper = string_int_char_dumper in
let typ = [ TString ; TInt; TChar ] in
let tfun = fun (s, i, c) -> [ of_string s ; of_int i; of_char c ] in
let def_features = (*PYF:t|T(s:S,i:I,c:C)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(s:S,i:I,c:C)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;



(*** String.uppercase ***)

let suppercaseRes = fun () ->
let name = "suppercase" in
let f = String.uppercase in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.lowercase ***)

let slowercaseRes = fun () ->
let name = "slowercase" in
let f = String.lowercase in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.capitalize ***)

let scapitalizeRes = fun () ->
let name = "scapitalize" in
let f = String.capitalize in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.uncapitalize ***)

let suncapitalizeRes = fun () ->
let name = "suncapitalize" in
let f = String.uncapitalize in
let arguments = [ "s" ] in
let tests = string_tests () in
let dumper = string_dumper in
let typ = [ TString ] in
let tfun = fun s -> [ of_string s ] in
let def_features = (*PYF:s|S*) in
let my_features = [] in
let def_postconditions = (*PYP:s|S|S*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;


(*** String.compare ***)

let scompare = fun (s0,s1) -> String.compare s0 s1;;

let scompareRes = fun () ->
let name = "scompare" in
let f = scompare in
let arguments = [ "s0" ; "s1" ] in
let tests = string_string_tests () in
let dumper = string_string_dumper in
let typ = [ TString ; TString ] in
let tfun = fun (s0, s1) -> [ of_string s0 ; of_string s1 ] in
let def_features = (*PYF:a|T(s0:S,s1:S)*) in
let my_features = [] in
let def_postconditions = (*PYP:a|T(s0:S,s1:S)|I*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_list
                           ~arg_names:arguments f tests features postconds trans
;;
