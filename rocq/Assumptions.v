(** * Assumptions: what the theorems of this workspace rest on

    [SkeletonApprox] is a functor over the evaluator [Eval]. Over a module declared at [Eval],
    each theorem's assumptions are that module's parameters and nothing else. *)

Require Import E4.Skeleton E4.SkeletonApprox.
Declare Module Ev : Eval.
Module A := Approx Ev.
Print Assumptions A.ofProgram_approx.
