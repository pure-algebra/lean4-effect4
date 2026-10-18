(* lane_eval.ml -- Lean's evaluator, as the realization of Rocq's in the extracted runner.

   What it is: the constants that docs/research/2026-10-16-itrees/rocq/LaneExtract.v realizes
   by `Extract Constant` (Denote.v's eval_term, decide, fail_exit, bad_shape and outside), each
   one Lean function lowered into ocaml/gen/api_gen.ml, and Rocq's exit type, which the extracted
   runner (rocq_run.ml) takes from here. So the comparison lane runs Rocq's tree with Lean's
   evaluator, and compares the trees.
   Depends on: Effect4_gen.Api_gen (generated), Eff_types.

   Properties:
   L1  Each realization is the Lean function its comment names; an exit crosses as Rocq's: a
       success as its value, a failure as Lean's exit image (reifyExitVal).  by construction *)

open Eff_types
module G = Effect4_gen.Api_gen

(* Denote.exitv *)
type exitv =
  | Success of Val.t
  | Failure of Val.t

let of_exit (ex : (Val.t, Err.t, Defect.t, int, unit) Exit.t) =
  match ex with
  | Exit.Success v -> Success v
  | ex -> Failure (G.reify_exit_val ex)
;;

(* Program.evalTerm *)
let eval_term (env : Val.t list) (t : Term.t) : Val.t option = G.program_eval_term env t

(* Rocq's eval_terms, eval_term's sibling in one fixpoint: extraction realizes the two
   together. Each term by evalTerm, all or none, as Denote.v writes it. *)
let rec eval_terms (env : Val.t list) (ts : Terms.t) : Val.t list option =
  match ts with
  | Terms.Nil -> Some []
  | Terms.Cons (t, rest) ->
    Option.bind (eval_term env t) (fun v ->
      Option.map (fun vs -> v :: vs) (eval_terms env rest))
;;

(* Decision.decide: what the arm binds, as Rocq's list of zero or one value *)
let decide (d : Decision.t) (v : Val.t) : (bool * Val.t list) option =
  Option.map (fun (b, bound) -> b, Option.to_list bound) (G.program_decision_decide d v)
;;

(* Exit.failure (Cause.fail (errOf v)), as Eval.fail writes it *)
let fail_exit (v : Val.t) : exitv =
  of_exit (Exit.Failure [ Reason.Fail (G.program_err_of v, []) ])
;;

(* Eval.badShape, Eval.outside *)
let bad_shape : exitv = of_exit G.run_tree_eval_bad_shape
let outside : exitv = of_exit G.run_tree_eval_outside
