open Batteries
open QCheck.Arbitrary
open TestGen
open Escher_types
open Escher_core
open Escher_components
open Escher_synth
open SpecInfer


(*** BatAvlTree.check ***)

let checkRes = fun ?(pind=(-1)) () ->
let name = "check" in
let f = BatAvlTree.check in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.is_empty ***)

let is_emptyRes = fun ?(pind=(-1)) () ->
let name = "is_empty" in
let f = BatAvlTree.is_empty in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.singleton_tree ***)

let singleton_treeRes = fun ?(pind=(-1)) () ->
let name = "singleton_tree" in
let f = BatAvlTree.singleton_tree in
let arguments = [ "v" ] in
let tests = int_tests () in
let dumper = int_dumper in
let typ = [ TInt ] in
let tfun = fun i -> [ of_int i ] in
let def_features = (*PYF:v|1*) in
let my_features = [] in
let def_postconditions = (*PYP:v|1|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.create ***)

let avlcreate = fun (l,v,r) -> BatAvlTree.create l v r;;

let createRes = fun ?(pind=(-1)) () ->
let name = "create" in
let f = avlcreate in
let arguments = [ "l" ; "v" ; "r" ] in
let tests = iavltree_int_iavltree_tests () in
let dumper = iavltree_int_iavltree_dumper in
let typ = [ TAVLTree ; TInt ; TAVLTree ] in
let tfun = fun (l,v,r) -> [ of_avltree of_int l ; of_int v ; of_avltree of_int r ] in
let def_features = (*PYF:t|T(l:R(1),v:1,r:R(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(l:R(1),v:1,r:R(1))|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.make_tree ***)

let avlmake_tree = fun (l,v,r) -> BatAvlTree.make_tree l v r;;

let make_treeRes = fun ?(pind=(-1)) () ->
let name = "make_tree" in
let f = avlmake_tree in
let arguments = [ "l" ; "v" ; "r" ] in
let tests = iavltree_int_iavltree_tests () in
let dumper = iavltree_int_iavltree_dumper in
let typ = [ TAVLTree ; TInt ; TAVLTree ] in
let tfun = fun (l,v,r) -> [ of_avltree of_int l ; of_int v ; of_avltree of_int r ] in
let def_features = (*PYF:t|T(l:R(1),v:1,r:R(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(l:R(1),v:1,r:R(1))|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.left_branch ***)

let left_branchRes = fun ?(pind=(-1)) () ->
let name = "left_branch" in
let f = BatAvlTree.left_branch in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.right_branch ***)

let right_branchRes = fun ?(pind=(-1)) () ->
let name = "right_branch" in
let f = BatAvlTree.right_branch in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.split_leftmost ***)

let split_leftmostRes = fun ?(pind=(-1)) () ->
let name = "split_leftmost" in
let f = BatAvlTree.split_leftmost in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|T(v:1,l:R(1))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.split_rightmost ***)

let split_rightmostRes = fun ?(pind=(-1)) () ->
let name = "split_rightmost" in
let f = BatAvlTree.split_rightmost in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|T(v:1,r:R(1))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.root ***)

let rootRes = fun ?(pind=(-1)) () ->
let name = "root" in
let f = BatAvlTree.root in
let arguments = [ "t" ] in
let tests = iavltree_tests () in
let dumper = iavltree_dumper in
let typ = [ TAVLTree ] in
let tfun = fun t -> [ of_avltree of_int t ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|1*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



(*** BatAvlTree.concat ***)

let avlconcat = fun (l,r) -> BatAvlTree.concat l r;;

let concatRes = fun ?(pind=(-1)) () ->
let name = "concat" in
let f = avlconcat in
let arguments = [ "l" ; "r" ] in
let tests = iavltree_iavltree_tests () in
let dumper = iavltree_iavltree_dumper in
let typ = [ TAVLTree ; TAVLTree ] in
let tfun = fun (l,r) -> [ of_avltree of_int l ; of_avltree of_int r ] in
let def_features = (*PYF:t|T(l:R(1),r:R(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(l:R(1),r:R(1))|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, dumper) ~record:name ~comps:default_avl
                           ~arg_names:arguments f tests features
                           (if pind = (-1) then postconds else [List.nth postconds pind]) trans
;;



let () =
    test_size := __TEST_SIZE__ ;
    max_conflict_set_size := __MAX_CONFLICT_SET_SIZE__ ;
    let run = (fun ((s, f) : (string * (?pind:int -> unit -> 'a))) ->
                  output_string stderr ("\n\n=== (" ^ (string_of_int __FUNCTION_INDEX__) ^ ") " ^ s ^ " ===\n") ;
                  print_specs stderr (f ~pind:__POST_INDEX__ ())) in
        run (List.nth [ ("BatAvlTree.check(t)", checkRes) ; ("BatAvlTree.is_empty(t)", is_emptyRes) ;
                        ("BatAvlTree.singleton_tree(v)", singleton_treeRes) ; ("BatAvlTree.create(l, v, r)", createRes) ;
                        ("BatAvlTree.make_tree(l, v, r)", make_treeRes) ; ("BatAvlTree.left_branch(t)", left_branchRes) ;
                        ("BatAvlTree.right_branch(t)", right_branchRes) ; ("BatAvlTree.split_leftmost(t)", split_leftmostRes) ;
                        ("BatAvlTree.split_rightmost(t)", split_rightmostRes) ; ("BatAvlTree.root(t)", rootRes) ;
                        ("BatAvlTree.concat(t0, t1)", concatRes) ] __FUNCTION_INDEX__)
