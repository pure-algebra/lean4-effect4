From Stdlib Require Import Extraction.
From Stdlib Require ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZBigInt ExtrOcamlNativeString.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Skeleton E4.EffExtract.

Extract Inlined Constant RocqOfOCaml.Basics.int => "Big_int_Z.big_int".
Extract Inlined Constant RocqOfOCaml.RocqOfOCaml.int => "Big_int_Z.big_int".

Module Lean <: Eval.
Include Eval.
End Lean.
Print Lean.
Extract Constant Lean.sync_op => "Rocq_gen.sync_op".
Extract Constant Lean.ctx => "Rocq_gen.ctx".
Extract Constant Lean.eval_push => "Rocq_gen.run_tree_eval_push".
Module Tree := Skeleton Lean.
Extraction "try2.ml" Tree.ofProgram.
