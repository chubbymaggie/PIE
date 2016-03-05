(* we use the Batteries Included OCaml package *)

open Batteries
open Escher_core
open Escher_components
open Escher_synth
open Escher_types

(* PAC learning a conjunction *)

(* a truth assignment is a mapping from boolean variables, which we represent by unique positive integers, to
   boolean values *)
type truthAssignment = (int, bool) BatHashtbl.t

(* thrown if there is no boolean function consistent with the given
   positive and negative examples.
   this happens in two situations:
     - a positive and negative example have the identical feature vector
     - there is no k-CNF formula (for some particular k being used) that distinguishes the positive and negative examples
*)
exception NoSuchFunction
exception BadCounterExample

let good_tests = ref 0
let conflict_counter = ref 0
let record_file = ref ""

let increment_record filename =
    (if Sys.file_exists filename then () else
        let oc = open_out filename in (
            output_string oc "0\n";
            close_out oc));
    let ic = open_in filename in
        let value = int_of_string (input_line ic) in (
            close_in ic;
            let oc = open_out filename in (
                output_string oc ((string_of_int (value + 1)) ^ "\n");
                close_out oc))

let string_of_truthAssignment ta =
  "[" ^ (BatHashtbl.fold (fun i b str -> str ^ "(" ^ (string_of_int i) ^ "," ^ (string_of_bool b) ^ "); ") ta "") ^ "]"

let hash_of_list l = BatHashtbl.of_enum(BatList.enum l)

(* return a list of numbers from start to stop, or the empty list if stop < start *)  
let range ?(start=1) stop =
  if stop < start then []
  else BatList.range start `To stop

(* return a list of numbers from stop to start, or the empty list if stop < start *)  
let rangeDown ?(start=1) stop =
  if stop < start then []
  else BatList.range stop `Downto start
(* remove literals from conj that are inconsistent with the given positive example *)
let pruneWithPositiveExamples (conj : int list) (example : truthAssignment) =
  BatList.filter (fun v -> BatHashtbl.find example v) conj

(* use a greedy heuristic to identify a set of literals in conj that cover all of the negative examples in
   remainingNeg (i.e., that conjunction of literals suffices to falsify all of the examples).
*)
let pruneWithNegativeExamples (conj : int list) (costs: (int, float) BatHashtbl.t) (remainingNeg : truthAssignment list) : int list =
  let rec helper conj remainingNeg accum =
    match remainingNeg with
      [] -> accum
      | _ ->
	  (* for each variable in conj, count how many of the negative examples it covers
	     (i.e, on how many of the examples it has the truth value false) *)
	  let counts =
	    BatList.map
	      (fun var ->
		 (var, BatList.fold_left
		    (fun c ex ->
		       if BatHashtbl.find_default ex var true then c else c+1) 0 remainingNeg)) conj in
	    (* find the variable with the largest inverted cost, computed as n/c where c is the cost of the variable
	       and n is the number of negative examples it covers
	    *)
	  let (chosenVar, maxCost) =
	    BatList.fold_left
	      (fun ((currChosen,currCost) as curr) ((v,n) as item) ->
		 let cost = float(n) /. (BatHashtbl.find costs v) in
		   if cost > currCost then (v,cost) else curr
	  ) (0,0.0) counts in

	    (* if no literals cover any of the remaining negative examples, then
	       there is no boolean function that properly classifies all of the original
	       positive and negative examples *)
	    if maxCost = 0.0 then raise NoSuchFunction else
      
	      (* keep the chosen variable and recurse,
		 filtering out this variable from the conjunction
		 and filtering out the negative examples that it covers.

		 we also filter out the negated version of the chosen
		 variable.  this is necessary when we are using this function
		 to find missing tests, so we don't say that (X and (not X))
		 is a missing test.  when this function is used as part of
		 learning a conjunction, there will be no negative variables
		 (see the comment on pacLearnConjunction about not including
		 negative literals), so it will be a no-op in that case.  *)

		helper
		  (BatList.filter (fun v -> v <> chosenVar && v <> -chosenVar) conj)
		  (BatList.filter (fun ex -> BatHashtbl.find_default ex chosenVar true) remainingNeg)
		  (chosenVar::accum)
  in
	      
    helper conj remainingNeg []


(* learn a simple conjunction that falsifies all negative examples but may not satisfy all positive examples
*)
let learnStrongConjunction (conj : int list) (costs: (int, float) BatHashtbl.t) (pos : truthAssignment list) (neg : truthAssignment list)
    : int list =

  let rec helper conj remainingNeg accum =
    match remainingNeg with
      [] -> accum
      | _ ->
	  (* for each variable in conj, count how many of the remaining negative examples it covers
	     (i.e, on how many of the examples it has the truth value false) *)
	  let counts =
	    BatList.map
	      (fun var ->
		 (var, BatList.fold_left
		    (fun c ex ->
		       if BatHashtbl.find_default ex var true then c else c+1) 0 remainingNeg)) conj in

	  (* find the variable with the largest count of covered negative examples.
	     note that currently we don't use the cost metric provided as an argument.
	    *)
	  let (chosenVar, maxCount) =
	    BatList.fold_left
	      (fun ((currChosen,currCount) as curr) ((v,count) as item) ->
		   if count > currCount then (v,count) else curr
	  ) (0,0) counts in

	    (* if no literals cover any of the remaining negative examples, then
	       we can't find a satisfiable boolean function that covers all of the original
	       negative examples.  not sure if that can ever happen. *)
	    if maxCount = 0 then raise NoSuchFunction else
      
	      (* keep the chosen variable and recurse,
		 filtering out this variable from the conjunction
		 and filtering out the negative examples that it covers.
	      *)
	      let newconj = BatList.filter (fun v -> v <> chosenVar) conj in
	      let newaccum = chosenVar::accum in

		if List.for_all (fun ta -> List.exists (fun i -> not (BatHashtbl.find ta i)) newaccum) pos
		  then
		      (* if the addition of chosenVar makes it so our result will not satisfy any positive tests,
			 then we throw out that chosenVar and keep looking *)
		      helper newconj remainingNeg accum
		  else
		      helper newconj (BatList.filter (fun ex -> BatHashtbl.find_default ex chosenVar true) remainingNeg) newaccum in
	      
    helper conj neg []

      
(* learn an unknown conjunct over the variables in list vars using the given set of
   positive and negative examples (list of truth assignments for which the unknown
   conjunct evaluates to true and false respectively).

   in the normal algorithm, you start with an initial conjunction of the form

     x1 and (not x1) and x2 and (not x2) and ... xn and (not xn)

   where the variables are x1...xn

   here we omit the negated ones because they are superfluous given our
   encoding of all possible disjuncts on the original variables as variables here
   (see the 3CNF learning algorithm below).

   so this is not a general algorithm for learning conjunctions

   if the flag strengthen is true, we attempt to find a conjunct that falsifies
   all negative examples and satisfies at least one positive example but might
   falsify others.  this is useful if we are trying to find a simple strengthening
   of the "true" precondition.

   costs is a map from variables to an integer cost, which is used as
   part of the greedy heuristic for learning from negative examples.
*)    
let pacLearnConjunction (strengthen : bool) (vars : int list) (costs: (int, float) BatHashtbl.t) (pos : truthAssignment list) (neg : truthAssignment list) =
  (* the initial conjunction is the AND of all variables *)
  let conj = vars in

    match strengthen with
	false ->
	  let conj = BatList.fold_left pruneWithPositiveExamples conj pos in
	    pruneWithNegativeExamples conj costs neg
      | true ->
	  learnStrongConjunction conj costs pos neg

    
(* PAC learning a CNF formula *)

(* produce all k-tuples (considered as sets) of numbers from 1 to n *)
let allKTuples k n =
  let rec aux k last rest = 
    match k with
	1 -> rest@last
      | _ ->
	  let next =
	    BatList.flatten (
	      BatList.map
		(fun (x::xs as l) -> BatList.map (fun v -> v::l) (rangeDown ~start:(x+1) n))
		last
	    ) in
	    aux (k-1) next (rest@last) in
  let tuples = aux k (BatList.map (fun x -> [x]) (rangeDown n)) [[]] in
    (* include all k-tuples with negative literals as well *)
    BatList.flatten (
      BatList.map 
	(fun tuple ->
	   BatList.fold_left
	     (fun curr x -> let x' = x+n in (BatList.map (fun l -> x::l) curr)@(BatList.map (fun l -> x'::l) curr))
	     [[]] tuple) tuples)


(* a type for cnf formulas, parameterized by the type used for atomic formulas *)    
type 'a literal = Pos of 'a | Neg of 'a
type 'a cnf = 'a literal list list

(* convert between representations for atomic formulas in a CNF formula *)
let mapCNF f clauses =
  BatList.map (fun clause ->
              BatList.map (fun lit ->
                         match lit with
			     Pos a -> Pos (f a)
			   | Neg a -> Neg (f a)) clause) clauses    

    
(* print a list, given a function to map each element to a string
   and a separator string to go between each element *)
let rec string_of_list_elems f sep l =
  BatString.concat sep (BatList.map f l)          

let string_of_clause_generic (string_of_a : 'a -> string) clause : string =
  let parenthesize s = "(" ^ s ^ ")" in
  let s =
    string_of_list_elems
      (fun lit ->
	 match lit with
	     Pos a -> string_of_a a
	   | Neg a -> "!(" ^ (string_of_a a) ^ ")")
      " || " clause in
    if (BatList.length clause) > 1 then parenthesize s else s 
    
let string_of_cnf_generic (string_of_a : 'a -> string) (cnf : 'a cnf) : string =
  match cnf with
      [] -> "true"
    | [[]] -> "false"
    | _ ->
	string_of_list_elems (string_of_clause_generic string_of_a) " && " cnf

let string_of_clause clause = string_of_clause_generic (fun x -> x) clause	  
let string_of_cnf cnf = string_of_cnf_generic (fun x -> x) cnf
	
exception ClauseEncodingError

(* given n variables over a k-CNF formula to learn, we create
   one variable per possible k-clause to use in the reduction to
   conjunction learning *)
let cnfVarsToConjunctVars k n : (int * (int list)) list =
    (* we use bit-packing to represent a clause (a set of ints) as a single int.
       our current encoding uses 10 bits per int and so requires:
        - 64-bit architecture
        - k <= 6
        - n*2 < 2^10 *)
  if Sys.word_size != 64 || k > 6 || n > 500 then raise ClauseEncodingError else

  let newVars = allKTuples k n in
  
  (* pack up to six into one int uniquely by bit-shifting *)
  BatList.map
    (fun t ->
       let (enc, _) = 
	 BatList.fold_left (fun (enc,b) x -> (enc lor (x lsl b), b+10)) (0,0) t in
	 (enc, t))
    newVars
  
(* PAC-learn a k-CNF formula over the variables numbered 1 to n, given
   a set of positive and negative examples (list of truth assignments, each represented as a list of
   (int, bool) pairs.

   if the flag strengthen is true, we attempt to find a formula that falsifies
   all negative examples and satisfies at least one positive example but might
   falsify others.  this is useful if we are trying to find a simple strengthening
   of the "true" precondition.

   
   costs associates a cost with each variable, which is used as a heuristic in the learning algorithm
*)
let pacLearnKCNF ?(k=3) (strengthen : bool) (n : int) (costs : (int, float) BatHashtbl.t)
    (pos : (int * bool) list list) (neg : (int * bool) list list) : int cnf =

  (* create one variable per possible k-clause over the given variables *)
  let varEncoding = cnfVarsToConjunctVars k n in

  (* create the costs of each new variable *)
  (* treat a negated literal as having the same cost as the positive one *)
  let _ = BatList.iter (fun i -> BatHashtbl.add costs (i+n) (BatHashtbl.find costs i)) (range n) in
  let costs = hash_of_list(
    (BatList.map
       (* TODO: a clause has the sum of the costs of its literals *)
       (fun (i, tuple) -> (i, 1.0 (* BatList.fold_left (fun c x -> c +. (BatHashtbl.find costs x)) 0.0 tuple *))) varEncoding)) in
    
  (* explicitly add truth values for negated literals to each example *)
  let augmentExamples examples =
    BatList.map
      (fun ex -> BatList.fold_left (fun curr ((i,b) as pos) -> pos::(i+n, not b)::curr) [] ex) examples in

  let (pos, neg) = (augmentExamples pos, augmentExamples neg) in

  (* translate an example on the original variables to one on the new variables *)
  let encodeExample ex =
    let hex = hash_of_list ex in
    hash_of_list(
      BatList.map
	(fun (i, tuple) ->
	  (i, BatList.exists (fun x -> BatHashtbl.find hex x) tuple)) varEncoding) in
    
  let newPos = BatList.map encodeExample pos in
  let newNeg = BatList.map encodeExample neg in

  (* learn a conjunction on the new variables *)
  let vars = BatList.map (fun (i,_) -> i) varEncoding in
  let learnedConjunct = pacLearnConjunction strengthen vars costs newPos newNeg in

  (* translate the result back to the old variables *)
  let decodeClause i =
    let rec aux n =
      match (i lsr n) land 0x3ff with
	  0 -> []
	| lit -> lit :: (aux (n+10))
    in aux 0
  in
  let learnedkCNF = BatList.map decodeClause learnedConjunct in

  (* convert the result into a slightly more palatable form *)
  let indexToLit i = if i <= n then Pos i else Neg (i-n) in
  let disjunctToClause tuple = BatList.map indexToLit tuple in
  BatList.map disjunctToClause learnedkCNF


    
(* PAC Learning Specifications *)

 (* cnfopt has type string cnf option
  * post has type string
  * *)
let print_spec chan (cnfopt, post) =
  match cnfopt with
      None -> output_string chan ("features are insufficient to separate positive and negative examples for postcondition " ^ post ^ "\n")
    | Some cnf ->
        output_string chan ("precondition: " ^ (string_of_cnf cnf) ^ "\n");
        output_string chan ("postcondition: " ^ post ^ "\n")

let print_specs chan specs =
  BatList.iter (fun s -> (print_spec chan s); output_string chan "\n") specs

let print_cnf chan cnfopt = match cnfopt with
    None -> output_string chan "false"
  | Some cnf -> output_string chan (string_of_cnf cnf)

(* the result of evaluating the function whose spec we are learning *)    
type 'a result = ('a, exn) BatResult.t

(* tests is a set of inputs on which to test a particular function
   features is a set of predicates on inputs that we use as features for our learning
   incompatible is a set of partial truth assignments for features that are never satisfiable.
   for that we refer to a feature by its number in the features list, and we refer to its negation
   by the negative of that number.
   the result is a small (according to the given costs) logical conjunction which none of the given tests satisfies.
*)
let missingTests ~tests:(tests : 'a list) ~features:(features : (('a -> bool) * 'b) list)
    ?(costs = hash_of_list(BatList.mapi (fun i _ -> (i+1, 1.0)) features)) ?(incompatible = []) ()
    : 'b literal list option =

  if features = [] then None else
  
  (* create the truth assignment corresponding to each test in tests by evaluating the features *)
  let examples =
    BatList.unique
      (BatList.map
	 (fun arg ->
	    (* if a feature throws an exception treat it as if the feature returns false *)
	    BatList.mapi (fun index (p,_) -> (index + 1, try p arg with _ -> false)) features) tests) in

  (* treat the incompatible assignments as if they are examples that we have already covered *)
  let examples = examples@incompatible in
    
  (* explicitly add to each truth assignment a mapping for negative literals.
     we treat -n as the negative version of variable n
  *)
  let examples =
    BatList.map
      (fun ex ->
	hash_of_list(
	  BatList.flatten (BatList.map (fun (n,b) -> [(n,b);(-n,not b)]) ex))) examples in

  let len = BatList.length features in

  let allvars = range len in
  let allvars = (BatList.map (fun i -> -i) allvars) @ allvars in

    (* negated literals have the same cost as the corresponding positive versions *)
  let _ = (BatList.iter (fun i -> BatHashtbl.add costs (-i) (BatHashtbl.find costs i)) (range len)) in

    try
      let missing = pruneWithNegativeExamples allvars costs examples in
	
	Some (BatList.map (fun i ->
			     let (_,s) = BatList.nth features ((BatInt.abs i)-1) in
			       if i>0 then Pos s else Neg s) missing)
    with
	NoSuchFunction -> None
	  

(* this function takes the same arguments as does pacLearnSpec except
   it takes only one postcondition rather than a list of them.  the
   function returns groups of tests that illustrate a missing
   feature. each group has the property that all inputs in the group
   lead to the same truth assignment of features, but the group
   contains at least one positive and one negative example (in terms
   of the truth value of the given postcondition).  hence the user
   needs to provide a new feature that can properly separate these
   positive and negative examples.
*)
   
let missingFeatures (f : 'a -> 'b) ~tests:(tests : 'a list) ~features:(features : (('a -> bool) * 'c) list)
    ~postcondition:((postcond, desc) : ('a -> 'b result -> bool) * 'c) =
  (* map each test input to its vector of feature booleans *)
  let examples =
    BatList.mapi
      (fun index arg ->
	 (* if a feature throws an exception treat it as if the feature returns false *)
	 (index, arg, (BatList.mapi (fun index (p,_) -> (index + 1, try p arg with _ -> false)) features))) tests in

  let grouped = BatList.group (fun (i1, arg1,ex1) (i2, arg2,ex2) -> compare ex1 ex2) examples in

  (* filter out groups of size 1 *)
  let grouped = BatList.filter (fun l -> (BatList.length l) > 1) grouped in

  (* compute the result value and associated postcondition truth value for each argument in a group *)
  let addPost = BatList.map (fun group ->
    BatList.map (fun (i, arg, ex) ->
      (if (i >= (List.length tests - (!good_tests))) then (arg, (BatResult.catch f arg), ex, true) else
      let res = BatResult.catch f arg in
				  try
				    let post = postcond arg res in
				    (arg, res, ex, post)
				  with
				      _ ->
					(arg, res, ex, false))) group) grouped in

  (* only keep the groups that have a conflict on the postcondition's truth value *)
  let filtered =
    BatList.filter
      (fun group ->
	(BatList.exists (fun (_,_,_,b) -> b) group) &&
	(BatList.exists (fun (_,_,_,b) -> not b) group)) addPost in

  filtered


exception Ambiguous_test of value list


let synthFeatures ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f : 'a -> 'b)
                  (missing_features : ('a * ('b, exn) BatResult.t * (int * bool) list * bool) list)
                  (postcond: ('a -> 'b result -> bool) * 'c) (trans: typ list * ('a -> value list))
                  : (('a -> bool) * 'c) list =

    if missing_features = [] then []
    else (
        if fname = "" then () else (
          let conflict_log = open_out (fname ^ "." ^ (string_of_int !conflict_counter) ^ ".con") in
            output_string conflict_log "\nData::\n";
            List.iter (fun (d,_,_,b) -> output_string conflict_log ((string_of_bool b) ^ " <= ");
                                        print_data conflict_log (VList ((snd trans) d));
                                        output_string conflict_log "\n")
                      missing_features;
            close_out(conflict_log));
        let tab = BatHashtbl.create (List.length missing_features) in
            BatList.iter (fun (i, _, _, b) ->
              try (if (BatHashtbl.find tab ((snd trans) i)) <> (VBool b) then raise (Ambiguous_test ((snd trans) i)))
              with Not_found -> BatHashtbl.add tab ((snd trans) i) (VBool b)) missing_features;
            prerr_string "\r    [%] Removing conflicts ... "; flush_all();
            let xtask = {
                target = {
                    domain = (fst trans);
                    codomain = TBool;
                    apply = (fun t -> try BatHashtbl.find tab t with _ -> VDontCare);
                    name = "synth";
                    dump = _unsupported_
                };
                inputs = BatList.mapi (fun i _ ->
                    ((if arg_names = []
                      then ((("x" ^ (string_of_int i) ^ "g"), (fun ars -> List.nth ars i)),
                            Leaf ("x" ^ (string_of_int i) ^ "g"))
                      else (((List.nth arg_names i), (fun ars -> List.nth ars i)),
                            Leaf (List.nth arg_names i))),
                    Array.of_list (BatHashtbl.fold (fun k _ acc -> (List.nth k i)::acc) tab []))) (fst trans);
                components = default_int @ default_string @ default_bool @ comps
            } in
            let solutions = solve xtask consts in
              (if fname = "" then () else
                let conflict_log = open_out_gen [Open_append] 0 (fname ^ "." ^ (string_of_int !conflict_counter) ^ ".con") in
                  conflict_counter := !conflict_counter + 1;
                  output_string conflict_log "\nSolutions::\n";
                  List.iter (fun (a,_) -> output_string conflict_log a; output_string conflict_log "\n") solutions;
                  close_out conflict_log;);
              (if !record_file = "" then () else increment_record (!record_file ^ ".escher"));
              List.map (fun (annot, func) -> (fun data -> (func (snd trans) data) = VBool true), annot) solutions)


(* default conflict group size *)
let max_conflict_set_size = ref 16
let resolveConflict ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f : 'a -> 'b)
                    (missing_features : ('a * ('b, exn) BatResult.t * (int * bool) list * bool) list)
                    (postcond: ('a -> 'b result -> bool) * 'c) (trans: typ list * ('a -> value list))
                    : (('a -> bool) * 'c) list =

    let final_mfs = if List.length missing_features < !max_conflict_set_size then missing_features else
        (let (good_mfs, bad_mfs) =
            List.fold_left (fun (g,b) mf -> match mf with (_,_,_,p) -> if p then ((mf::g),b) else (g,(mf::b)))
                           ([],[]) missing_features in
            let final_good_mfs = BatList.take (!max_conflict_set_size / 2) good_mfs in
            let final_bad_mfs = BatList.take (!max_conflict_set_size / 2) bad_mfs in
                final_good_mfs @ final_bad_mfs) in
        synthFeatures ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f final_mfs postcond trans


(* try to resolve the first group of conflicting tests that can be resolved *)
let rec convergeOneMissingFeature ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f: 'a -> 'b)
                                  (missing_features: ('a * ('b, exn) BatResult.t * (int * bool) list * bool) list list)
                                  (postcond: ('a -> 'b result -> bool) * 'c) (trans: typ list * ('a -> value list))
                                  : (('a -> bool) * 'c) list =

    if missing_features = [] then []
    else let new_features = resolveConflict ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f (List.hd missing_features) postcond trans
            in if not (new_features = []) then new_features
            else convergeOneMissingFeature ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f (List.tl missing_features) postcond trans


(* try to resolve all groups of conflicting tests for one post condition*)
  let rec convergePCondFeatures ?(fname="") ?(consts=[]) ?(comps=[]) ?(arg_names=[]) (f: 'a -> 'b) (tests : 'a list)
                                (features: (('a -> bool) * 'c) list) (postcond: ('a -> 'b result -> bool) * 'c)
                                (trans: typ list * ('a -> value list)) :(('a -> bool) * 'c) list =

    let all_missing_features = missingFeatures f tests features postcond in
        if all_missing_features = []
        then features
        else let mf = convergeOneMissingFeature ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f all_missing_features postcond trans
             in if mf = [] then features else convergePCondFeatures ~fname:fname ~consts:consts ~comps:comps ~arg_names:arg_names f tests (features @ mf) postcond trans


(* a postcondition should raise this exception to indicate that the given test input should be ignored *)
exception IgnoreTest

(* k is the maximum clause length for the formula we will provide (i.e., it's a k-cnf formula)
   f is the function whose spec we are inferring
   tests is a set of inputs on which to test f
   features is a set of predicates on inputs that we use as features for our learning

   if the flag strengthen is true, we attempt to find a formula that falsifies
   all negative examples and satisfies at least one positive example but might
   falsify others.  this is useful if we are trying to find a simple strengthening
   of the "actual" precondition.

   costs is an optional mapping from the nth feature (numbered 1 through N according to their order) to
     a cost (float) - lower is better
   post is the postcondition whose corresponding precondition formula we are trying to learn
   we associate some kind of description (of polymorphic type 'c) with each feature and postcondition
*)
let pacLearnSpec ?(k=3) ?(strengthen=false) (f : 'a -> 'b) ~tests:(tests : 'a list) ~features:(features : (('a -> bool) * 'c) list)
    ?(costs = hash_of_list(BatList.map (fun v -> (v,1.0)) (range (BatList.length features))))
    (post : ('a -> 'b result -> bool) * 'c) : 'c cnf option * 'c =

  let featureLen = BatList.length features in
  prerr_string ("\r    [%] Inferring {" ^ (snd post) ^ "} [k = " ^ (string_of_int k) ^ "] (" ^ (string_of_int featureLen) ^ "f x " ^ (string_of_int (List.length tests)) ^ "t) ...                                     "); flush_all();

  (* create the truth assignment corresponding to each test in tests by evaluating the features *)
  let examples =
    BatList.map
      (fun arg ->
	 (* if a feature throws an exception treat it as if the feature returns false *)
	 BatList.mapi (fun index (p,_) -> (index + 1, try p arg with _ -> false)) features) tests in

  (* run all the tests to get their outputs *)
  let testResults = BatList.mapi (fun i test -> (i, test, BatResult.catch f test)) tests in


  let pacLearnOne (postcond, str) =

  (* separate the tests into positive and negative examples *)
    let (pos, neg) =
      BatList.fold_left2 (fun (l1,l2) (i, arg, res) ex ->
        try if ((i >= (List.length tests - (!good_tests))) || postcond arg res)
            then (ex::l1,l2)
            else (l1,ex::l2)
        with IgnoreTest -> (l1,l2) | _ -> (l1,ex::l2))
        ([],[]) testResults examples in
      
    (* remove duplicates *)
    let (pos, neg) = (BatList.unique pos, BatList.unique neg) in

      try
	let cnf = pacLearnKCNF ~k:k strengthen featureLen costs pos neg in
	let precond = mapCNF (fun i -> let (_,s) = BatList.nth features (i-1) in s) cnf in
	(Some precond, str)
      with
	  NoSuchFunction -> (None, str) in

  pacLearnOne post

let rec pacLearnSpecIncrK ?(k=1) (f: 'a -> 'b) (tests: 'a list) (features : (('a -> bool) * 'c) list)
    (post : ('a -> 'b result -> bool) * 'c) : 'c cnf option * 'c =

  let res = pacLearnSpec ~k:k f ~tests:tests ~features:features post in
    if fst res <> None then res
    else (try pacLearnSpecIncrK ~k:(k+1) f tests features post with ClauseEncodingError -> (Some [[Pos "~~ FAILED ~~"]], snd post))


let resolveAndPacLearnSpec ?(k=1) ?(dump=("", (fun a -> ""))) ?(record="") ?(consts=[]) ?(comps=[])
                           ?(arg_names=[]) (f: 'a -> 'b) (tests: 'a list)
                           (features : (('a -> bool) * 'c) list) (posts : (('a -> 'b result -> bool) * 'c) list)
                           (trans : typ list * ('a -> value list)) : ('c cnf option * 'c) list =

  record_file := record;
  if fst dump = "" then () else (
    conflict_counter := 0;
    Sys.command("rm -rf " ^ (fst dump) ^ ".*.con");
    let test_file = open_out ((fst dump) ^ ".tests") in
      List.iter (fun t -> output_string test_file (((snd dump) t) ^ "\n")) tests;
      close_out test_file);

  List.map (fun post ->
    (* remove all tests which throw IgnoreTest *)
    let tests = (List.fold_left (fun p t -> try (fst post) t (BatResult.catch f t) ; (t::p) with IgnoreTest -> p) [] tests) in (
      prerr_string ("\r    [%] " ^ (snd post) ^ " -> Escher: "); flush_all();
      let res = pacLearnSpecIncrK ~k:k f tests
                                  (if fst trans = [] then features
                                   else convergePCondFeatures ~fname:(fst dump) ~consts:consts ~comps:comps
                                                              ~arg_names:arg_names f tests features post trans)
                                  post in
        (output_string stderr "\n" ; print_spec stderr res ; res)
    )) posts


let rec escherSynthAndVerify ?(dump=("", (fun a -> ""))) ?(record="") ?(consts=[]) ?(comps=[])
                             (f : 'a -> 'b) (tests : 'a list) (post : ('a -> 'b result -> bool) * 'c)
                             (trans : typ list * ('a -> value list)) (trans_test: 'z -> 'a)
                             (smtfile : string): (('a -> bool) * string) =

    (* We would never have IgnoreTest exception in this case *)

  record_file := record;
  (if fst dump = "" then () else (
    let test_file = open_out ((fst dump) ^ ".tests") in
      List.iter (fun t -> output_string test_file (((snd dump) t) ^ "\n")) tests;
      close_out test_file));

  let target = {
        domain = (fst trans);
        codomain = TBool;
        apply = (fun t -> VBool(f (trans_test t)));
        name = "synth";
        dump = _unsupported_
      } in
  let rec helper tests = (
    let xtask = {
       target = target;
       inputs = BatList.mapi (fun i _ ->
          (((("x" ^ (string_of_int i) ^ "g"), (fun ars -> List.nth ars i)),
            Leaf ("x" ^ (string_of_int i) ^ "g")),
           Array.of_list (List.map (fun k -> (List.nth ((snd trans) k) i)) tests))) (fst trans);
        components = default_int @ default_string @ default_bool @ comps
    } in
    prerr_string ("\r    [*] Synthesizing --- "); flush_all();
    let sol = List.hd (solve xtask consts) in
      (if !record_file = "" then () else increment_record (!record_file ^ ".escher"));
      let our_output = open_out (smtfile ^ ".xour") in
        output_string our_output (fst sol) ;
        close_out our_output ;
        Sys.command ("./var_replace " ^ smtfile ^ ".tml < " ^ smtfile ^ ".xour > " ^ smtfile ^ ".your") ;
        prerr_string ("\r    [?] Verifying --- ");
        let candidate = open_in (smtfile ^ ".your") in (prerr_string (input_line candidate) ; close_in candidate);
        prerr_string "                            \n" ; flush_all();
        Sys.command ("./verify " ^ smtfile ^ ".your " ^ smtfile ^ " 1 0 " ^ !record_file ^ "> " ^ smtfile ^ ".zour") ;
        let res_file = open_in (smtfile ^ ".zour") in
          if input_line res_file = "UNSAT" then (close_in res_file ; ((fun data -> ((snd sol) (snd trans) data) = VBool true), (fst sol)))
          else (close_in res_file ;
                Sys.command("./var_replace revVals " ^ smtfile ^ ".tml < " ^ smtfile ^ ".zour > " ^ smtfile ^ ".our") ;
                let res_file = open_in (smtfile ^ ".our") in
                let args = (List.map (fun vtyp -> let data = input_line res_file in match vtyp with TInt -> VInt(int_of_string data) | TString -> VString(data)) (fst trans)) in
                prerr_string "      [+] Added test ... "; print_data stderr (VList(args)); prerr_string "\n";
                close_in res_file;
                if (try f (trans_test args) with _ -> false) then raise BadCounterExample else (helper ((trans_test args) :: tests)))
  ) in helper tests


let rec pacLearnSpecAndVerify ?(k=1) ?(dump=("", (fun a -> ""))) ?(record="") ?(consts=[]) ?(unsats=[])
                              ?(comps=[]) (f : 'a -> 'b) (tests : 'a list) (features : (('a -> bool) * 'c) list)
                              (post : ('a -> 'b result -> bool) * 'c) (trans : typ list * ('a -> value list))
                              (trans_test: 'z -> 'a) (smtfile : string): 'c cnf option =

    (* We would never have IgnoreTest exception in this case *)

  (if (!good_tests < 1) then (good_tests := List.length tests) else ());
  record_file := record;
  (if fst dump = "" then () else (
    conflict_counter := 0;
    Sys.command("rm -rf " ^ (fst dump) ^ ".*.con");
    let test_file = open_out ((fst dump) ^ ".tests") in
      List.iter (fun t -> output_string test_file (((snd dump) t) ^ "\n")) tests;
      close_out test_file));

  let rec helper k unsats tests features = (
    let features =
      if fst trans = [] then features
      else (try convergePCondFeatures ~fname:(fst dump) ~consts:consts ~comps:comps f tests features post trans
            with Ambiguous_test(value_list) ->
              let ambiguous_out = open_out("ambiguous") in
              print_data ambiguous_out (VList(value_list));
              close_out ambiguous_out; [])
    in

    if missingFeatures f tests features post <> [] then None else (
      let res = fst (pacLearnSpec ~k:k f ~tests:tests ~features:features post) in
      if res = None then (
        helper (k + 1) unsats tests features
      (* TODO: res is FALSE, add new model ::
        let mtests = missingTests tests features ~incompatible:unsats in
          if mtests = None then res
          else (
            let Some missing = mtests in
            let our_output = open_out (smtfile ^ ".xour") in
              output_string our_output (fst missing) ;
              close_out our_output ;
              Sys.command ("./var_replace " ^ smtfile ^ ".tml < " ^ smtfile ^ ".xour > " ^ smtfile ^ ".your") ;
              Sys.command ("./chkSAT " ^ smtfile ^ ".your > " ^ smtfile ^ ".zour ") ;
              let res_file = open_in (smtfile ^ ".zour") in
                if input_line res_file = "UNSAT"
                then (close_in res_file ;
                      let fvector = Array.mapi (fun i _ -> (i+1, false)) (Array.create (List.length features) (0, false)) in
                        BatList.fold_left (fun _ f -> match f with Pos i -> fvector.(i-1) <- (i, true) | _ -> ()) () (snd missing);
                        pacLearnSpecAndVerify ~k:k f tests features post trans iconsts trans_test smtfile ~unsats:((Array.to_list fvector)::unsats))
                else (close_in res_file ;
                      Sys.command("./var_replace revVals " ^ smtfile ^ ".tml " ^ (string_of_int (List.length (fst trans))) ^ " < " ^ smtfile ^ ".zour > " ^ smtfile ^ ".our") ;
                      let res_file = open_in (smtfile ^ ".our") in
                        let tests = (trans_test (List.map (fun _ -> int_of_string (input_line res_file)) (fst trans))) :: tests in
                          (close_in res_file ;
                           pacLearnSpecAndVerify ~k:k f tests features post trans iconsts trans_test smtfile ~unsats:unsats))) *)
      ) else (
        let our_output = open_out (smtfile ^ ".xour") in
          print_cnf our_output res ;
          close_out our_output ;
          Sys.command ("./var_replace " ^ smtfile ^ ".tml < " ^ smtfile ^ ".xour > " ^ smtfile ^ ".your") ;
          prerr_string ("\r    [?] Verifying [k = " ^ (string_of_int k) ^ "] --- ");
          let candidate = open_in (smtfile ^ ".your") in (prerr_string (input_line candidate) ; close_in candidate);
          prerr_string "                            \n" ; flush_all();
          Sys.command ("./verify " ^ smtfile ^ ".your " ^ smtfile ^ " 1 0 " ^ !record_file ^ " > " ^ smtfile ^ ".zour") ;
          let res_file = open_in (smtfile ^ ".zour") in
            if input_line res_file = "UNSAT" then (close_in res_file ; res)
            else (close_in res_file ;
                  Sys.command("./var_replace revVals " ^ smtfile ^ ".tml < " ^ smtfile ^ ".zour > " ^ smtfile ^ ".our") ;
                  let res_file = open_in (smtfile ^ ".our") in
                  let args = (List.map (fun vtyp -> let data = input_line res_file in match vtyp with TInt -> VInt(int_of_string data) | TString -> VString(data)) (fst trans)) in
                  prerr_string "      [+] Added test ... "; print_data stderr (VList(args)); prerr_string "\n";
                  close_in res_file;
                  if f (trans_test args) then raise BadCounterExample else (helper 1 unsats ((trans_test args) :: tests) features)))))
  in helper k unsats tests features
