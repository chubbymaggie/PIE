#use "top_helper.ml"

(*** BatAvlTree.create ***)

let avlcreate = fun (l,v,r) -> BatAvlTree.create l v r;;

let createRes = fun () ->
let name = "create" in
let f = avlcreate in
let tests = iavltree_int_iavltree_tests () in
let typ = [ TInt ; TInt ; TInt ] in
let tfun = fun (l,v,r) -> [ of_int (BatAvlTree.height l) ; of_int v ; of_int (BatAvlTree.height r) ] in
let def_features = [] in
let my_features = [
  (* We are not interested in features over v *)
  ((fun (l,v,r) -> (BatAvlTree.height l) > 0), "lh > 0");
  ((fun (l,v,r) -> (BatAvlTree.height l) = 0), "lh = 0");
  ((fun (l,v,r) -> (BatAvlTree.height l) < 0), "lh < 0");
  ((fun (l,v,r) -> (BatAvlTree.height r) > 0), "rh > 0");
  ((fun (l,v,r) -> (BatAvlTree.height r) = 0), "rh = 0");
  ((fun (l,v,r) -> (BatAvlTree.height r) < 0), "rh < 0");
  ((fun (l,v,r) -> BatAvlTree.is_empty l), "empty l");
  ((fun (l,v,r) -> BatAvlTree.is_empty r), "empty r");
] in
let def_postconditions = [] in
let my_postconditions = [
  ((fun z r -> match r with Bad _ -> true | _ -> false), "exception thrown")
] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_int_iavltree_dumper) ~record:name f tests features postconds trans
;;
