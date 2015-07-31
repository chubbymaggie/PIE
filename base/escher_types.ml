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
  | TUnknown

type value =
  | VInt of int
  | VBool of bool
  | VChar of char
  | VList of value list
  | VTree of bin_tree
  | VString of string
  | VError
  | VDontCare

let typeof v = match v with
  | VInt(_)    -> TInt
  | VBool(_)   -> TBool
  | VChar(_)   -> TChar
  | VList(_)   -> TList
  | VTree(_)   -> TTree
  | VString(_) -> TString
  | _          -> TUnknown

let of_int i = VInt(i)
let of_bool b = VBool(b)
let of_char c = VChar(c)
let of_string s = VString(s)
let of_tree btree = VTree(btree)
let of_list f l = VList(List.map f l)

let wrap_escher_type transformer data =
  transformer data
