open Batteries
open QCheck.Arbitrary
open TestGen
open Escher_types
open Escher_core
open Escher_components
open Escher_synth
open Pie

let buzzfizzRes = fun ?(pind=(-1)) () ->
let name = "buzzfizz" in
let f = (fun n ->
  if n mod 15 = 0 then "buzzfizz"
  else if n mod 3 = 0 then "buzz"
  else if n mod 5 = 0 then "fizz"
  else "") in
let arguments = [ "n" ] in
let tests = generate (1 -- 1024) in
let dumper = int_dumper in
let typ = [ TInt ] in
let tfun = fun n -> [ of_int n ] in
let def_features = (*PYF:n|I*) in
let my_features = [] in
let def_postconditions = [(*disabled: PYP:s|S|I *)] in
let my_postconditions = [
  ((fun _ r -> match r with Bad _ -> raise IgnoreTest
                       | Ok z -> z = "buzz"),
   "is buzz") ;
  ((fun _ r -> match r with Bad _ -> raise IgnoreTest
                       | Ok z -> z = "fizz"),
   "is fizz") ;
  ((fun _ r -> match r with Bad _ -> raise IgnoreTest
                       | Ok z -> z = "buzzfizz"),
   "is buzzfizz") ;     
  ((fun _ r -> match r with Bad _ -> raise IgnoreTest
                       | Ok z -> try (BatString.find z "fizz"); true with _ -> false),
   "has fizz")
] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
  resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name
                         ~comps:(unsafe_modulo::default_int) ~arg_names:arguments f tests features
                         (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let () =
    test_size := __TEST_SIZE__ ;
    max_conflict_set_size := __MAX_CONFLICT_SET_SIZE__ ;
    let run = (fun ((s, f) : (string * (?pind:int -> unit -> 'a))) ->
                  output_string stderr ("\n\n=== (" ^ (string_of_int __FUNCTION_INDEX__) ^ ") " ^ s ^ " ===\n") ;
                  print_specs stderr (f ~pind:__POST_INDEX__ ())) in
        run (List.nth [ ("buzzfizz(n)", buzzfizzRes) ] __FUNCTION_INDEX__)
