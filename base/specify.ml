open Batteries

open Escher_types
open Escher_core
open Escher_components
open Escher_synth

let gen_post_conds ((in_vals, out_val) : 'a * 'b)
                   ((in_names, in_types) : string list * typ list)
                   ((out_name, out_type) : string * typ)
                   ((in_trans, out_trans) : ('a -> value list) * ('b -> value)) =
  let escher_in = in_trans in_vals in
  let synthed =
    solve ~ast:true {
      target = {
        domain = out_type::in_types;
        codomain = TBool;
        apply = (fun x -> VBool true);
        name = "post";
        dump = _unsupported_
      };
      inputs = (((out_name, (fun ars -> List.nth ars 0)), (Leaf out_name)), [| out_trans out_val ; out_trans out_val |])
               ::(List.mapi (fun i n -> (((n, (fun ars -> List.nth ars (i+1))), (Leaf n)),
                                        [| List.nth escher_in i ; List.nth escher_in i |]))
                  in_names);
      components = default_components
    } []
  in List.map (fun (a, f) -> ((fun ins out -> match out with
                                 Bad _ -> false
                               | Ok res -> (f (fun (o,i) -> (out_trans o)::(in_trans i)) (res, ins) = VBool true)), a))
              (List.filter (fun (a, _) -> BatString.exists a out_name) synthed)

let specify f tests features (dom, codom) (ins, out) (in_trans, out_trans) iconsts =
  let posts = gen_post_conds (List.hd tests, f (List.hd tests)) (ins, dom) (out, codom) (in_trans, out_trans)
  in pacLearnSpec f ~tests:tests ~features:features posts
