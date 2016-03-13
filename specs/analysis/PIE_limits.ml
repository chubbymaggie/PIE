open Batteries
open QCheck.Arbitrary
open TestGen
open Escher_types
open Escher_core
open Escher_components
open Escher_synth
open Pie


let test_PIE_success = fun (k :int) (fcount :int) ->
  let name = ("limit" ^ (string_of_int k)) in
  let f = (fun a -> List.length a) in
  let arguments = [ "a" ] in
  let tests = intList_tests () in
  let dumper = intList_dumper in
  let typ = [ TList ] in
  let tfun = fun t -> [ of_list of_int t ] in
  let def_features = [
    ((fun a -> (List.length a) = 0), "len(a) > 0")
  ] in
  let def_postconditions = [] in

  let my_features = (
    let rec features fs count =
      match count with
        0 -> fs
      | _ -> features (((fun _ -> true), "true") :: fs) (count - 1)
    in features [] (fcount - 1)
  ) in
  let my_postconditions = [
    ((fun i z -> match z with
        Bad _ -> false
      | Ok r -> r = 0), "Zero length")
  ] in

  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in

  resolveAndPacLearnSpec ~k:k ~dump:(name, dumper) ~record:name
                         ~arg_names:arguments f tests features postconds trans
;;

let () =
  test_PIE_success (int_of_string (Sys.argv.(1)))
                   (int_of_string (Sys.argv.(2)));
  ()
