open Batteries
open Escher_components
open Escher_core
open Escher_types

exception Success

type task = {
  target : component;
  inputs : Vector.t list;
  components : component list }

let rec divide f arity target acc =
  if arity = 0 then
    if target = 0 then f acc else ()
  else begin
    for i = 1 to target do
      divide f (arity - 1) (target - i) (i::acc)
    done
  end

(* Rename to "divide" if using the "depth" heuristic, which violates our
   additivity assumption *)
let rec divide_depth f arity target acc =
  if arity = 0 then f acc
  else if arity = 1 && List.for_all (fun x -> x < target) acc
       then f (target::acc)
       else begin
         for i = 0 to target do
           divide f (arity - 1) target (i::acc)
         done
       end


(* Upper bound on the heuristic value a solution may take *)
let max_h = ref 16

let expand_ = ref "size"
let goal_graph = ref false

let noisy = ref false
let quiet = ref true

let all_solutions = ref []

let rec is_boring = function
  | (Leaf "0") | (Leaf "[]") -> true
  | (Leaf _) -> false
  | Node (_, args) -> List.for_all is_boring args

let rec fancy = function
  | Leaf _ -> 1
  | Node (x, args) ->
      let h_values = List.map fancy args in
      let h_sum = List.fold_left (+) 0 h_values in
      let size = h_sum in (* estimate size with h_sum *)
      let penalty = 0 in
      let penalty =
        if size <= 3 then penalty
        else if is_boring (Node (x, args)) then 2 + penalty
             else penalty
      in 1 + h_sum + penalty

let hvalue ((_,x),_) =
  match !expand_ with
    | "size" -> program_size x
    | "depth" -> program_height x
    | "fancy" -> fancy x
    | _ -> failwith "Unrecognized expand method!"

type goal_status =
  | Closed of Vector.t
  | Open

and goal = {
  varray : value array;
  mutable status : goal_status; }

let short_goal_string goal = match goal.status with
  | Open -> "<open> " ^ (varray_string goal.varray)
  | Closed v -> "<closed> " ^ (Vector.string v)

let rec print_goal indent goal =
  if String.length indent > 10 then print_endline (indent ^ "...")
  else print_endline (indent ^ "goal: " ^ (varray_string goal.varray))

let solve_impl ?ast:(ast=false) task consts =
  let seen = ref VSet.empty in
  let vector_size = Array.length (snd (List.hd task.inputs)) in
  let components = task.components in

  let final_goal = {
    varray = snd (apply_component task.target task.inputs);
    status = Open; } in

  let goals = ref (VArrayMap.add final_goal.varray final_goal VArrayMap.empty) in

  let close_goal vector goal =
    if !noisy then begin
      print_endline ("Closed goal " ^ (varray_string goal.varray));
      print_endline ("       with " ^ (Vector.string vector));
      end else ();
    goal.status <- Closed vector;
    match final_goal.status with Closed cls -> (all_solutions := cls::all_solutions.contents; if not ast then raise Success else ()) | _ -> ()
  in

  let int_array = Array.make !max_h VSet.empty in
  let bool_array = Array.make !max_h VSet.empty in
  let char_array = Array.make !max_h VSet.empty in
  let list_array = Array.make !max_h VSet.empty in
  let tree_array = Array.make !max_h VSet.empty in
  let string_array = Array.make !max_h VSet.empty in

  let check_vector v =
    (* Close all matching goals *)
    let (v_closes, _) = partition_map (varray_matches ~typeonly:ast (snd v)) (!goals)
    in if !noisy then begin
         print_endline "--- new vector --------------------------------------";
         print_endline ((string_of_int (hvalue v)) ^ ": " ^ (Vector.string v));
       end else ();
       List.iter (close_goal v) v_closes; true
  in

  let int_components = List.filter (fun c -> c.codomain = TInt) components in
  let bool_components = List.filter (fun c -> c.codomain = TBool) components in
  let char_components = List.filter (fun c -> c.codomain = TChar) components in
  let list_components = List.filter (fun c -> c.codomain = TList) components in
  let tree_components = List.filter (fun c -> c.codomain = TTree) components in
  let string_components = List.filter (fun c -> c.codomain = TString) components in

  let apply_comp f types i =
    let rec apply_cells types acc locations = match types, locations with
      | (typ::typs, i::locs) -> VSet.iter (fun x -> apply_cells typs (x::acc) locs) begin
          match typ with
            | TInt -> int_array.(i)
            | TBool -> bool_array.(i)
            | TChar -> char_array.(i)
            | TList -> list_array.(i)
            | TTree -> tree_array.(i)
            | TString -> string_array.(i)
          end
      | ([], []) -> f (List.rev acc)
      | _ -> failwith "Impossible!"
    in divide (apply_cells types []) (List.length types) (i-1) []
  in
  let expand_component c array i =
    let f x =
      let vector = apply_component c x in
      let h_value = hvalue vector in
      let has_err = Array.fold_left (fun p x -> match x with VError -> true | _ -> p) false (snd vector) in
      if (h_value < !max_h && (not has_err))
      then ((if not (!noisy) then ()
            else print_endline (string_of_int h_value ^ ">>" ^ (Vector.string vector)));
            array.(h_value) <- VSet.add vector (array.(h_value)))
    in apply_comp f c.domain i
  in
  let expand_type (mat, components) i =
    List.iter (fun c -> expand_component c mat i) components;
  in
  let expand i =
    List.iter (fun x -> expand_type x i)
              [(int_array, int_components);
               (bool_array, bool_components);
               (char_array, char_components);
               (list_array, list_components);
               (tree_array, tree_components);
               (string_array, string_components)]
  in
  let zero = ((("0", (fun ars -> VInt 0)), Leaf "0"), Array.make vector_size (VInt 0)) in
  let nil = ((("[]", (fun ars -> VList [])), Leaf "[]"), Array.make vector_size (VList [])) in
  let btrue = ((("true", (fun ars -> VBool true)), Leaf "true"), Array.make vector_size (VBool true)) in
  let bfalse = ((("false", (fun ars -> VBool false)), Leaf "false"), Array.make vector_size (VBool false)) in
  if !quiet then () else (
    print_endline ("Inputs: ");
    List.iter (fun v -> print_endline ("   " ^ (Vector.string v))) task.inputs;
    print_endline ("Goal: " ^ (varray_string final_goal.varray)));
  list_array.(1)   <- VSet.singleton nil;
  int_array.(1)    <- List.fold_left (fun p i -> VSet.add ((((string_of_int i), (fun ars -> VInt i)), Leaf ("const_" ^ (string_of_int i))), Array.make vector_size (VInt i)) p)
                      (VSet.singleton zero) (BatList.sort_unique compare (1::(BatList.filter_map (fun v -> match v with VInt x -> Some x | _ -> None) consts)));
  string_array.(1) <- List.fold_left (fun p s -> VSet.add (((("\"" ^ s ^ "\""), (fun ars -> VString s)), Leaf ("const_\"" ^ s ^ "\"")), Array.make vector_size (VString s)) p)
                      (VSet.empty) (BatList.sort_unique compare (BatList.filter_map (fun v -> match v with VString x -> Some x | _ -> None) consts));
  bool_array.(1)   <- VSet. add btrue (VSet.singleton bfalse);
  List.iter (fun input ->
    let array = match (snd input).(1) with
      | VList _ -> list_array
      | VInt _ -> int_array
      | VBool _ -> bool_array
      | VChar _ -> char_array
      | VTree _ -> tree_array
      | VString _ -> string_array
      | VError -> failwith "Error in input"
      | VDontCare -> failwith "Underspecified input"
    in array.(1) <- VSet.add input array.(1))
  task.inputs;
  for i = 2 to !max_h-1; do
    list_array.(i-1) <- VSet.filter check_vector list_array.(i-1);
    int_array.(i-1) <- VSet.filter check_vector int_array.(i-1);
    bool_array.(i-1) <- VSet.filter check_vector bool_array.(i-1);
    char_array.(i-1) <- VSet.filter check_vector char_array.(i-1);
    tree_array.(i-1) <- VSet.filter check_vector tree_array.(i-1);
    string_array.(i-1) <- VSet.filter check_vector string_array.(i-1);
    begin match final_goal.status with
      | Closed p -> final_goal.status <- Open
      | Open -> () end;
    (if !quiet then prerr_string else print_endline) (" @" ^ (string_of_int i)); flush_all();
    if !noisy then begin
      let print_goal k _ = print_endline (" * " ^ (varray_string k)) in
        print_endline ("Goals: ");
        VArrayMap.iter print_goal (!goals);
    end else ();
    expand i;
  done

  let solve ?ast:(ast=false) task consts =
    all_solutions := [] ;
  (try solve_impl ~ast:ast task consts with Success -> ());
  if not (!quiet) then (print_endline "Synthesis Result: "; List.iter (fun v -> print_endline (Vector.string v)) all_solutions.contents) ;
  List.rev_map (fun (((x,y),_),_) -> (x, (fun trans data -> y (trans data)))) all_solutions.contents

  let default_int = [plus;mult;minus;geq;leq;lt;gt;equal;modulo ; addone;subone (*; iabs *)]
  let default_list = [empty;tail;head;cat;cons;length;reverse;listHas;listEq]
  let default_bool = [notc;orc;andc]
  let default_char = [cequal]

  let default_tree = [tree_val;is_leaf;tree_left;tree_right;tree_node;tree_leaf]
  let default_string = [str_eq; str_sub; str_get; str_concat; str_contains; (* str_index_of; *) str_len; str_replace]

  let default_components = default_int @ default_bool @ default_string @ default_list
  (* default_int @ default_bool @ default_list @ default_string @ default_char *)

  let int_list xs = VList (List.map (fun x -> VInt x) xs)

  let palindrome_task = {
    target = palindrome;
    inputs = [((("x", (fun ars -> List.hd ars)), Leaf "x"), [| VList [VBool true]; VList [VBool true; VBool false]; int_list []; int_list [6]; int_list [4;6]; int_list [6;4;6]; int_list [2;6;4;6]|])];
    components = default_components @ default_list
  }

  (* PACSpec Examples *)

  let absPrecond_task =
    { target = absPrecond;
    inputs = [((("x", (fun ars -> List.hd ars)), Leaf "x"), [| VInt 0; VInt 1; VInt (-1)|])];
    components = default_components }

  let test_task = {
    target = {
      domain = [TInt];
        codomain = TBool;
        apply = (fun [VInt x] -> VBool (x - 1 < 1));
        name = "test";
        dump = _unsupported_
    };
    inputs = [((("x", (fun ars -> List.hd ars)), Leaf "x"), [| VInt 1; VInt 2; VInt (-1) |])];
    components = default_components
    }

  let synthesis_targets = [absPrecond_task; palindrome_task]

  let synthesize target =
    let task =
      try List.find (fun x -> x.target.name = target) synthesis_targets
    with Not_found ->
      if not (!quiet) then (print_endline ("Task `" ^ target ^ "' not found.  Available tasks:");
      List.iter (fun task -> print_endline task.target.name) synthesis_targets);
      raise Not_found
        in
    solve task []; ()

  let target =
    ("-target", Arg.String synthesize, " Synthesize a target program")

  let expand_method =
    ("-expand", Arg.Set_string expand_, " Set expand method")

  let noisy_arg =
    ("-noisy", Arg.Set noisy, " Print additional information")

  let quiet_arg =
    ("-quiet", Arg.Set quiet, " Print less information")

  let no_goal_graph_arg =
    ("-no-goal-graph", Arg.Clear goal_graph, " Disable goal graph")

  let spec_list =
    [ target;
    expand_method;
    no_goal_graph_arg;
    noisy_arg;
    quiet_arg;
    ]
  let usage_msg = "todo"
  let anon_fun s = raise (Arg.Bad (s ^ " is not recognized"))

  let _ = Arg.parse (Arg.align spec_list) anon_fun usage_msg
