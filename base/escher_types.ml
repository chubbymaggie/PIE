open Batteries

type bin_tree =
  | BTLeaf of int
  | BTNode of int * bin_tree * bin_tree

type typ =
  | TInt
  | TBool
  | TChar
  | TList
  | TTree
  | TString
  | TAVLTree
  | TUnknown

type value =
  | VInt of int
  | VBool of bool
  | VChar of char
  | VList of value list
  | VTree of bin_tree
  | VString of string
  | VAVLTree of value BatAvlTree.tree
  | VError
  | VDontCare

let typeof v = match v with
  | VInt(_)     -> TInt
  | VBool(_)    -> TBool
  | VChar(_)    -> TChar
  | VList(_)    -> TList
  | VTree(_)    -> TTree
  | VString(_)  -> TString
  | VAVLTree(_) -> TAVLTree
  | _           -> TUnknown

let of_int i = VInt(i)
let of_bool b = VBool(b)
let of_char c = VChar(c)
let of_string s = VString(s)
let of_tree btree = VTree(btree)
let of_list f l = VList(List.map f l)
let rec of_avltree f t = if BatAvlTree.is_empty t then VAVLTree(BatAvlTree.empty)
                         else let ((VAVLTree l), (VAVLTree r)) = (
                                (of_avltree f (BatAvlTree.left_branch t)),
                                (of_avltree f (BatAvlTree.right_branch t))
                              ) in VAVLTree (BatAvlTree.create l (f (BatAvlTree.root t)) r)

let from_int = function | VInt(i) -> i
let from_bool = function | VBool(b) -> b
let from_char = function | VChar(c) -> c
let from_string = function | VString(s) -> s
let from_tree = function | VTree(t) -> t
let from_list f = function | VList(l) -> List.map f l
let rec from_avltree f = function | VAVLTree(t) -> if BatAvlTree.is_empty t then t else
                                                   BatAvlTree.create (from_avltree f (VAVLTree (BatAvlTree.left_branch t)))
                                                                     (f (BatAvlTree.root t))
                                                                     (from_avltree f (VAVLTree (BatAvlTree.right_branch t)))

let rec print_data chan (data: value) : unit = match data with
    VError       -> output_string chan "- ERROR -"
  | VDontCare    -> output_string chan "- UNKNOWN -"
  | VTree(tree)  -> output_string chan "- TREE -"
  | VString(str) -> output_string chan ("\"" ^ str ^ "\"")
  | VInt(i)      -> output_string chan (string_of_int i)
  | VBool(b)     -> output_string chan (string_of_bool b)
  | VChar(c)     -> output_char chan c
  | VList(vl)    -> (output_string chan "[ ";
                     (if vl = [] then ()
                     else (print_data chan (List.hd vl);
                       List.iter (fun v -> output_string chan ", ";
                                           print_data chan v)
                                 (List.tl vl)));
                     output_string chan " ]")
  | VAVLTree(t)   -> (output_string chan "{";
                      (if BatAvlTree.is_empty t then ()
                      else (print_data chan (VAVLTree (BatAvlTree.left_branch t));
                            output_string chan " (";
                            print_data chan (BatAvlTree.root t);
                            output_string chan ") ";
                            print_data chan (VAVLTree (BatAvlTree.right_branch t))));
                      output_string chan "}")
