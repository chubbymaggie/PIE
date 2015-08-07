#use "top_helper.ml"
  
(* INFERRING RELATIONSHIPS BETWEEN STANDARD AND EXTRA STRING FUNCTIONS *)

(* various flavors of equality for two function call results *)

let eqNormalResult (v1,v2) =
  match (v1, v2) with 
    | (Ok r1, Ok r2) -> r1 = r2
    | _ -> raise IgnoreTest


let eqNormalResultStrict (v1,v2) =
  match (v1, v2) with 
    | (Ok r1, Ok r2) -> r1 = r2
    | (Bad _, Bad _) -> raise IgnoreTest
    | _ -> false

let eqResult (v1,v2) =
  match (v1, v2) with 
    | (Ok r1, Ok r2) -> r1 = r2
    | (Bad _, Bad _) -> true
    | _ -> false
	
	
(* from the stringext library *)

let drop s n =
  let l = String.length s in
  if n >= l
  then ""
  else String.sub s n (l - n)

let take s n =
  if n >= String.length s
  then s
  else String.sub s 0 n

let stakeRes = fun () ->
let (f: (string * int * int * int) -> ((string, exn) BatResult.t * (string, exn) BatResult.t)) =
    (fun (s,n,i1,i2) ->  (BatResult.catch (fun () -> String.sub s i1 i2) (), BatResult.catch (fun () -> take s n) ())) in
let tests = distinct_string_int_int_int_tests in
let typ = [ TString ; TInt ; TInt ; TInt ] in
let tfun = fun (s, n, i1, i2) -> [ of_string s ; of_int n ; of_int i1 ; of_int i2] in
let def_features = (*PYF:t|T(s:S,n:I,i1:I,i2:I)*) in
let my_features = [] in
let def_postconditions = [
  ((fun z r -> eqNormalResult(BatResult.get r)), "normal results are equal");
  ((fun z r -> eqNormalResultStrict(BatResult.get r)), "normal strict results are equal")
] in
let my_postconditions = []
in
let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
       resolveAndPacLearnSpec f tests features postconds trans []
;;


let sdropRes = fun () ->
let (f: (string * int * int * int) -> ((string, exn) BatResult.t * (string, exn) BatResult.t)) =
    (fun (s,n,i1,i2) ->  (BatResult.catch (fun () -> String.sub s i1 i2) (), BatResult.catch (fun () -> drop s n) ())) in
let tests = distinct_string_int_int_int_tests in
let typ = [ TString ; TInt ; TInt ; TInt ] in
let tfun = fun (s, n, i1, i2) -> [ of_string s ; of_int n ; of_int i1 ; of_int i2] in
let def_features = (*PYF:t|T(s:S,n:I,i1:I,i2:I)*) in
let my_features = [] in
let def_postconditions = [
  ((fun z r -> eqNormalResult(BatResult.get r)), "normal results are equal");
  ((fun z r -> eqNormalResultStrict(BatResult.get r)), "normal strict results are equal")
] in
let my_postconditions = []
in
let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
       resolveAndPacLearnSpec f tests features postconds trans []
;;


let ssliceRes = fun () ->
let f = (fun (s,i1,i2,f,l) -> (BatResult.catch (fun () -> String.sub s i1 i2) (), BatResult.catch (fun () -> BatString.slice ~first:f ~last:l s) ())) in
let tests = distinct_string_int_int_int_int_tests in
let typ = [ TString ; TInt ; TInt ; TInt ; TInt ] in
let tfun = fun (s, i1, i2, f, l) -> [ of_string s ; of_int i1 ; of_int i2; of_int f ; of_int l] in
let def_features = (*PYF:t|T(s:S,i1:I,i2:I,f:I,l:I)*) in
let my_features = [] in
let def_postconditions = [
  ((fun z r -> eqNormalResult(BatResult.get r)), "normal results are equal");
  ((fun z r -> eqNormalResultStrict(BatResult.get r)), "normal strict results are equal")
] in
let my_postconditions = []
in
let trans = (typ, tfun) in
    let features = def_features @ my_features in
    let postconds = def_postconditions @ my_postconditions in
       resolveAndPacLearnSpec f tests features postconds trans []
;;
