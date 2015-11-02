open Batteries

open Escher_core
open Escher_types

let _unsupported_ = (fun l -> " **UNSUPPORTED** ")

type component = {
      domain : typ list;
      codomain : typ;
      apply : value list -> value;
      name : string;
      dump : string list -> string
    }

let apply_component (c : component) (args : Vector.t list) =
  if (c.name = "not" && (match (snd (fst (List.hd args)))
                         with Node ("not", _) -> true | _ -> false))
  || (c.name = "addone" && (match (snd (fst (List.hd args)))
                            with Node ("subone", _) -> true | _ -> false))
  || (c.name = "subone" && (match (snd (fst (List.hd args)))
                            with Node ("addone", _) -> true | _ -> false))
  || (c.name = "mod" && (match (snd (fst List.(hd (tl args))))
                         with Node _ -> true | Leaf x -> not (BatString.starts_with x "const_")))
  || (c.name = "mult" && (match ((snd (fst List.(hd args))), (snd (fst List.(hd (tl args)))))
                          with (Node _, Node _) -> true
                             | (Node _, Leaf a) -> not (BatString.starts_with a "const_")
                             | (Leaf a, Node _) -> not (BatString.starts_with a "const_")
                             | (Leaf a, Leaf b) -> not (BatString.((starts_with a "const_") || (starts_with b "const_")))))
  then ((("", (fun _ -> VBool false)), Node ("", [])), Array.mapi (fun _ _ -> VError) (snd (List.hd args)))
  else (
    let select i l = List.map (fun x -> x.(i)) l in
    let prs = List.map (fun (((_,x),_),_) -> x) args in
    let values = List.map snd args in
    let new_prog = fun ars -> c.apply (List.map (fun p -> p ars) prs) in
    let new_str = c.dump (List.map (fun (((x,_),_),_) -> x) args) in
    let result = Array.mapi (fun i _ -> c.apply (select i values)) (List.hd values)
    in (((new_str, new_prog), Node (c.name, List.map (fun ((_,x),_) -> x) args)), result))

(* Default INT components *)
let addone = {
    domain = [TInt];
    codomain = TInt;
    apply = (function
             | [VInt x] -> VInt (x + 1)
             | _      -> VError);
    name = "addone";
    dump = (fun l -> "(" ^ (List.hd l) ^ " + 1)")
}

let subone = {
    domain = [TInt];
    codomain = TInt;
    apply = (function
             | [VInt x] -> VInt (x - 1)
             | _      -> VError);
    name = "subone";
    dump = (fun l -> "(" ^ (List.hd l) ^ " - 1)")
}

let iabs = {
  domain = [TInt];
  codomain = TInt;
  apply = (function
           | [VInt x] -> VInt (abs x)
           | _ -> VError);
  name = "abs";
  dump = (fun l -> "(abs " ^ (List.hd l) ^ ")")
}

let plus = {
    domain = [TInt; TInt];
    codomain = TInt;
    apply = (function
             | [VInt x; VInt y] -> VInt (x + y)
             | _ -> VError);
    name = "plus";
    dump = (fun l -> "(" ^ (List.hd l) ^ " + " ^ List.(hd (tl l)) ^ ")")
}

let minus = {
    domain = [TInt; TInt];
    codomain = TInt;
    apply = (function
             | [VInt x; VInt y] -> VInt (x - y)
             | _ -> VError);
    name = "minus";
    dump = (fun l -> "(" ^ (List.hd l) ^ " - " ^ List.(hd (tl l)) ^ ")")
}

let mult = {
    domain = [TInt; TInt];
    codomain = TInt;
    apply = (function
             | [VInt x; VInt y] -> VInt (x * y)
             | _ -> VError);
    name = "mult";
    dump = (fun l -> "(" ^ (List.hd l) ^ " * " ^ List.(hd (tl l)) ^ ")")
}

let leq = {
    domain = [TInt;TInt];
    codomain = TBool;
    apply = (function
             | [VInt x; VInt y] -> VBool (x <= y)
             | _ -> VError);
    name = "leq";
    dump = (fun l -> "(" ^ (List.hd l) ^ " <= " ^ List.(hd (tl l)) ^ ")")
}

let geq = {
    domain = [TInt;TInt];
    codomain = TBool;
    apply = (function
             | [VInt x; VInt y] -> VBool (x >= y)
             | _ -> VError);
    name = "leq";
    dump = (fun l -> "(" ^ (List.hd l) ^ " >= " ^ List.(hd (tl l)) ^ ")")
}

let lt = {
    domain = [TInt;TInt];
    codomain = TBool;
    apply = (function
             | [VInt x; VInt y] -> VBool (x < y)
             | _ -> VError);
    name = "leq";
    dump = (fun l -> "(" ^ (List.hd l) ^ " < " ^ List.(hd (tl l)) ^ ")")
}

let gt = {
    domain = [TInt;TInt];
    codomain = TBool;
    apply = (function
             | [VInt x; VInt y] -> VBool (x > y)
             | _ -> VError);
    name = "leq";
    dump = (fun l -> "(" ^ (List.hd l) ^ " > " ^ List.(hd (tl l)) ^ ")")
}

let equal = {
    domain = [TInt;TInt];
    codomain = TBool;
    apply = (function
             | [VInt x;VInt y] -> VBool (x = y)
             | _ -> VError);
    name = "equal";
    dump = (fun l -> "(" ^ (List.hd l) ^ " = " ^ List.(hd (tl l)) ^ ")")
}

let modulo = {
    domain = [TInt;TInt];
    codomain = TInt;
    apply = (function
             | [VInt x;VInt y] -> if y < 2 then VError else VInt (((x mod y) + y) mod y)
             | _ -> VError);
    name = "mod";
    dump = (fun l -> "(" ^ (List.hd l) ^ " % " ^ List.(hd (tl l)) ^ ")")
}


(* Default BOOL components *)
let notc = {
    domain = [TBool];
    codomain = TBool;
    apply = (function
             | [VBool x] -> VBool (not x)
             | _ -> VError);
    name = "not";
    dump = (fun l -> "(! " ^ (List.hd l) ^ ")")
}

let andc = {
  domain = [TBool;TBool];
    codomain = TBool;
    apply = (function
             | [VBool x; VBool y] -> VBool (x && y)
             | _ -> VError);
    name = "and";
    dump = (fun l -> "(" ^ (List.hd l) ^ " & " ^ (List.hd (List.tl l)) ^ ")")
}

let orc = {
  domain = [TBool;TBool];
    codomain = TBool;
    apply = (function
             | [VBool x; VBool y] -> VBool (x || y)
             | _ -> VError);
    name = "or";
    dump = (fun l -> "(" ^ (List.hd l) ^ " | " ^ (List.hd (List.tl l)) ^ ")")
}


(* Default CHAR components *)
let cequal = {
    domain = [TChar;TChar];
    codomain = TBool;
    apply = (function
             | [VChar x;VChar y] -> VBool (x = y)
             | _ -> VError);
    name = "cequal";
    dump = (fun l -> "(" ^ (List.hd l) ^ " = " ^ List.(hd (tl l)) ^ ")")
}


(* Default LIST components *)
let length = {
    domain = [TList];
    codomain = TInt;
    apply = (function
             | [VList xs] -> VInt (List.length xs)
             | _ -> VError);
    name = "length";
    dump = (fun l -> "(len " ^ (List.hd l) ^ ")")
}

let empty = {
    domain = [TList];
    codomain = TBool;
    apply = (function
             | [VList x] -> VBool (List.length x = 0)
             | _ -> VError);
    name = "empty?";
    dump = (fun l -> "(" ^ (List.hd l) ^ " = [])")
}

let reverse = {
    domain = [TList];
    codomain = TList;
    apply = (function
             | [VList x] -> VList (List.rev x)
             | _ -> VError);
    name = "reverse";
    dump = (fun l -> "(rev " ^ (List.hd l) ^ ")")
}

let cons = {
    domain = [TInt; TList];
    codomain = TList;
    apply = (function
             | [VInt x; VList xs] -> VList (VInt x::xs)
             | _ -> VError);
    name = "cons";
    dump = (fun l -> "(" ^ (List.hd l) ^ " :: " ^ (List.hd (List.tl l)) ^ ")")
}

let head = {
    domain = [TList];
    codomain = TInt;
    apply = (function
             | [VList (x::_)] -> x
             | _ -> VError);
    name = "head";
    dump = (fun l -> "(hd " ^ (List.hd l) ^ ")")
}

let tail = {
    domain = [TList];
    codomain = TList;
    apply = (function
             | [VList (_::xs)] -> VList xs
             | _ -> VError);
    name = "tail";
    dump = (fun l -> "(tl " ^ (List.hd l) ^ ")")
}

let cat = {
    domain = [TList; TList];
    codomain = TList;
    apply = (function [VList xs; VList ys] -> VList (xs @ ys)
             | _ -> VError);
    name = "cat";
    dump = (fun l -> "(" ^ (List.hd l) ^ " @ " ^ (List.hd (List.tl l)) ^ ")")
}

let listHas = {
    domain = [TInt; TList];
    codomain = TBool;
    apply = (function [x ; VList xs] -> VBool (List.mem x xs)
             | _ -> VError);
    name = "cat";
    dump = (fun l -> "(" ^ (List.hd l) ^ " in " ^ (List.hd (List.tl l)) ^ ")")
}

let listEq = {
    domain = [TList;TList];
    codomain = TBool;
    apply = (function
             | [VList x; VList y] -> VBool (x=y)
             | _ -> VError);
    name = "listEq";
    dump = (fun l -> "(" ^ (List.hd l) ^ " = " ^ (List.hd (List.tl l)) ^ ")")
}

(* Default TREE components *)
let is_leaf = {
    domain = [TTree];
    codomain = TBool;
    apply = (function
             | [VTree (BTLeaf _)] -> VBool true
             | [VTree (BTNode (_,_,_))] -> VBool false
             | _ -> VError);
    name = "is_leaf";
    dump = _unsupported_
}

let tree_val = {
    domain = [TTree];
    codomain = TInt;
    apply = (function
             | [VTree (BTLeaf x)] -> VInt x
             | [VTree (BTNode (x,_,_))] -> VInt x
             | _ -> VError);
    name = "tree_val";
    dump = _unsupported_
}

let tree_left = {
    domain = [TTree];
    codomain = TTree;
    apply = (function
             | [VTree (BTNode (_,left,_))] -> VTree left
             | _ -> VError);
    name = "tree_left";
    dump = _unsupported_
}

let tree_right = {
    domain = [TTree];
    codomain = TTree;
    apply = (function
             | [VTree (BTNode (_,_,right))] -> VTree right
             | _ -> VError);
    name = "tree_right";
    dump = _unsupported_
}

let tree_node = {
    domain = [TInt; TTree; TTree];
    codomain = TTree;
    apply = (function
             | [VInt v; VTree l; VTree r] -> VTree (BTNode (v, l, r))
             | _ -> VError);
    name = "tree_node";
    dump = _unsupported_
}

let tree_leaf = {
    domain = [TInt];
    codomain = TTree;
    apply = (function
             | [VInt n] -> VTree (BTLeaf n)
             | _ -> VError);
    name = "tree_leaf";
    dump = _unsupported_
}

(* String components *)

let str_get = {
    domain = [TString;TInt];
    codomain = TChar;
    apply = (function
             | [VString str; VInt i] ->
                   begin try VChar (String.get str i)
                   with Invalid_argument _ -> VError end
             | _ -> VError);
    name = "str_get";
    dump = (fun l -> "(#get(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ "))")
}

let str_concat = {
    domain = [TString;TString];
    codomain = TString;
    apply = (function
             | [VString x; VString y] -> VString (x ^ y)
             | _ -> VError);
    name = "str_concat";
    dump = (fun l -> "(#cat(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ "))")
}


let str_eq = {
    domain = [TString;TString];
    codomain = TBool;
    apply = (function
             | [VString x; VString y] -> VBool (x = y)
             | _ -> VError);
    name = "str_eq";
    dump = (fun l -> "(#eql(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ "))")
}

let str_contains = {
    domain = [TString;TString];
    codomain = TBool;
    apply = (function
             | [VString s; VString t] -> VBool (BatString.exists s t)
             | _ -> VError);
    name = "str_contains";
    dump = (fun l -> "(#has(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ "))")
}

let str_index_of = {
    domain = [TString;TString];
    codomain = TInt;
    apply = (function
             | [VString s; VString t] ->
                 begin try VInt (BatString.find s t)
                       with Not_found -> VInt (-1) end
             | _ -> VError);
    name = "str_index_of";
    dump = (fun l -> "(#ind(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ "))")
}

let str_len = {
    domain = [TString];
    codomain = TInt;
    apply = (function
             | [VString x] -> VInt (String.length x)
             | _ -> VError);
    name = "str_len";
    dump = (fun l -> "(#len(" ^ (List.hd l) ^ "))")
}

let str_replace = {
  domain = [TString;TString;TString];
    codomain = TString;
    apply = (function
             | [VString str; VString src ; VString dst] -> VString (snd (BatString.replace str src dst))
             | _ -> VError);
    name = "str_replace";
    dump = (fun l -> "(#rep(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ ", " ^ (List.hd (List.tl (List.tl l))) ^ "))")
}

let str_sub = {
    domain = [TString;TInt;TInt];
    codomain = TString;
    apply = (function
             | [VString str; VInt lo; VInt len] ->
                   begin try VString (String.sub str lo len)
                   with _ -> VError end
             | _ -> VError);
    name = "str_sub";
    dump = (fun l -> "(#sub(" ^ (List.hd l) ^ ", " ^ (List.hd (List.tl l)) ^ ", " ^ (List.hd (List.tl (List.tl l))) ^ "))")
}

(* not using these for now *)

let str_prefix = {
    domain = [TString;TInt];
    codomain = TString;
    apply = (function
             | [VString str; VInt hi] ->
                   begin try VString (String.sub str 0 hi)
                   with Invalid_argument _ -> VError end
             | _ -> VError);
    name = "str_prefix";
    dump = (fun l -> "(pre " ^ (List.hd l) ^ " " ^ (List.hd (List.tl l)) ^ ")")
}

let str_suffix = {
    domain = [TString;TInt];
    codomain = TString;
    apply = (function
             | [VString str; VInt lo] ->
                   begin try VString (String.sub str lo ((String.length str) - lo))
                   with Invalid_argument _ -> VError end
             | _ -> VError);
    name = "str_suffix";
    dump = (fun l -> "(suf " ^ (List.hd l) ^ " " ^ (List.hd (List.tl l)) ^ ")")
}

let rec palindrome_impl l =
  l = (List.rev l)

let palindrome = {
    domain = [TList];
    codomain = TBool;
    apply = (function
               [VList l] -> VBool (palindrome_impl l)
             | _ -> VError);
    name = "palindrome";
    dump = _unsupported_
}

(* PACSpec Examples *)

let absPrecond = {
    domain = [TInt];
    codomain = TBool;
    apply = (function
             | [VInt x] -> if x = 1 then VBool false else if x = 0 then VBool true else if x = (-1) then VBool true else VError
             | _ -> VError);
    name = "absPrecond";
    dump = _unsupported_
}
