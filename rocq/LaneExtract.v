(** The comparison lane extracts the generated control skeleton.

    [SkeletonApprox.v] proves budget monotonicity over this same [Skeleton.v].
    The lane compares Rocq extraction with LCNF lowering on finitely many runs.
    It shares Lean's evaluator and tree runner, and does not compare those implementations.
    [EffExtract.v] maps the program types to their owner, [Eff_types].
    [Rocq_gen] exports the evaluator's lowered operations, with no hand evaluator.
    Rocq's budget [nat] maps to OCaml [int]; the lane supplies only bounded budgets.
    Program naturals and integers map to Zarith through [ExtrOcamlZBigInt]. *)

From Stdlib Require Import Extraction.
From Stdlib Require ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZBigInt ExtrOcamlNativeString.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Skeleton E4.EffExtract.

Extract Inlined Constant RocqOfOCaml.Basics.int => "Big_int_Z.big_int".
Extract Inlined Constant RocqOfOCaml.RocqOfOCaml.int => "Big_int_Z.big_int".

Module Lean <: Eval.
Include Eval.
End Lean.

Extract Constant Lean.sync_op => "Rocq_gen.sync_op".
Extract Constant Lean.ctx => "Rocq_gen.ctx".
Extract Constant Lean.eval_push => "Rocq_gen.run_tree_eval_push".
Extract Constant Lean.eval_test => "Rocq_gen.run_tree_eval_test".
Extract Constant Lean.eval_badShape => "Rocq_gen.run_tree_eval_bad_shape".
Extract Constant Lean.eval_value => "Rocq_gen.run_tree_eval_value".
Extract Constant Lean.eval_term => "Rocq_gen.run_tree_eval_term".
Extract Constant Lean.eval_programs => "Rocq_gen.run_tree_eval_programs".
Extract Constant Lean.eval_exitVal => "Rocq_gen.run_tree_eval_exit_val".
Extract Constant Lean.eval_outside => "Rocq_gen.run_tree_eval_outside".
Extract Constant Lean.eval_fail => "Rocq_gen.run_tree_eval_fail".
Extract Constant Lean.eval_failCause => "Rocq_gen.run_tree_eval_fail_cause".
Extract Constant Lean.eval_sync => "Rocq_gen.run_tree_eval_sync".
Extract Constant Lean.eval_inTable => "Rocq_gen.run_tree_eval_in_table".
Extract Constant Lean.eval_body => "Rocq_gen.run_tree_eval_body".
Extract Constant Lean.eval_arg => "Rocq_gen.run_tree_eval_arg".
Extract Constant Lean.eval_cellOp => "Rocq_gen.run_tree_eval_cell_op".
Extract Constant Lean.eval_choose => "Rocq_gen.run_tree_eval_choose".
Extract Constant Lean.eval_pushAll => "Rocq_gen.run_tree_eval_push_all".
Extract Constant Lean.eval_causeVal => "Rocq_gen.run_tree_eval_cause_val".
Extract Constant Lean.eval_caught => "Rocq_gen.run_tree_eval_caught".
Extract Constant Lean.eval_restore => "Rocq_gen.run_tree_eval_restore".
Extract Constant Lean.eval_provide => "Rocq_gen.run_tree_eval_provide".
Extract Constant Lean.eval_contextVal => "Rocq_gen.run_tree_eval_context_val".
Extract Constant Lean.eval_root => "Rocq_gen.run_tree_eval_root".

Module Tree := Skeleton Lean.
Extraction "rocq_run.ml" Tree.ofProgram.
