#use "top_helper.ml"



(*** BatAvlTree.check ***)

let checkRes = fun () ->
let name = "check" in
let f = BatAvlTree.check in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun i -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.is_empty ***)

let is_emptyRes = fun () ->
let name = "is_empty" in
let f = BatAvlTree.is_empty in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun i -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|B*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.singleton_tree ***)

let singleton_treeRes = fun () ->
let name = "singleton_tree" in
let f = BatAvlTree.singleton_tree in
let tests = int_tests () in
let typ = [ TInt ] in
let tfun = fun i -> [ of_int i ] in
let def_features = (*PYF:v|1*) in
let my_features = [] in
let def_postconditions = (*PYP:v|1|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, int_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.create ***)

let avlcreate = fun (l,v,r) -> BatAvlTree.create l v r;;

let createRes = fun () ->
let name = "create" in
let f = avlcreate in
let tests = iavltree_int_iavltree_tests () in
let typ = [ TInt ; TInt ; TInt ] in
let tfun = fun (l,v,r) -> [ of_int (BatAvlTree.height l) ; of_int v ; of_int (BatAvlTree.height r) ] in
let def_features = (*PYF:t|T(l:R(1),v:1,r:R(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(l:R(1),v:1,r:R(1))|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_int_iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.make_tree ***)

let avlmake_tree = fun (l,v,r) -> BatAvlTree.make_tree l v r;;

let make_treeRes = fun () ->
let name = "make_tree" in
let f = avlmake_tree in
let tests = iavltree_int_iavltree_tests () in
let typ = [ TInt ; TInt ; TInt ] in
let tfun = fun (l,v,r) -> [ of_int (BatAvlTree.height l) ; of_int v ; of_int (BatAvlTree.height r) ] in
let def_features = (*PYF:t|T(l:R(1),v:1,r:R(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(l:R(1),v:1,r:R(1))|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_int_iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.left_branch ***)

let left_branchRes = fun () ->
let name = "left_branch" in
let f = BatAvlTree.left_branch in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun t -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.right_branch ***)

let right_branchRes = fun () ->
let name = "right_branch" in
let f = BatAvlTree.right_branch in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun t -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.split_leftmost ***)

let split_leftmostRes = fun () ->
let name = "split_leftmost" in
let f = BatAvlTree.split_leftmost in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun t -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|T(v:1,l:R(1))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.split_rightmost ***)

let split_rightmostRes = fun () ->
let name = "split_rightmost" in
let f = BatAvlTree.split_rightmost in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun t -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|T(v:1,r:R(1))*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.root ***)

let rootRes = fun () ->
let name = "root" in
let f = BatAvlTree.root in
let tests = iavltree_tests () in
let typ = [ ] in
let tfun = fun t -> [ ] in
let def_features = (*PYF:t|R(1)*) in
let my_features = [] in
let def_postconditions = (*PYP:t|R(1)|1*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_dumper) ~record:name f tests features postconds trans
;;



(*** BatAvlTree.concat ***)

let avlconcat = fun (l,r) -> BatAvlTree.concat l r;;

let concatRes = fun () ->
let name = "concat" in
let f = avlconcat in
let tests = iavltree_iavltree_tests () in
let typ = [ ] in
let tfun = fun (l,r) -> [ ] in
let def_features = (*PYF:t|T(l:R(1),r:R(1))*) in
let my_features = [] in
let def_postconditions = (*PYP:t|T(l:R(1),r:R(1))|R(1)*) in
let my_postconditions = [] in
  let trans = (typ, tfun) in
  let features = def_features @ my_features in
  let postconds = def_postconditions @ my_postconditions in
    resolveAndPacLearnSpec ~dump:(name, iavltree_iavltree_dumper) ~record:name f tests features postconds trans
;;




