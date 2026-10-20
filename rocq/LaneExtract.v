(** * LaneExtract: Rocq's budgeted runner as OCaml, for the comparison lane

    Extracts [Api.run_at] under two host functions, one for the cells and one for the rows
    ([Api.route], [Api.fn_host], and [cells_fn] here), at the program types of the estate:
    [E4.EffExtract], which [rocq/tools/split_types.ml --extract] prints from
    [ocaml/eff/eff_types.ml], sends each type of [Eff_types.v] back to its owner's module.
    [make gen-rocq-lane] compiles this file over the lane's development and writes its output,
    [rocq_run.ml] and its interface, to [ocaml/engine/test/rocq/] (GENERATED). The lane compares it
    with Lean's call tree lowered by LCNF ([Effect4.Run.Tree.probe] in [ocaml/gen/api_gen.ml]),
    budget by budget.

    The extracted code is Rocq's tree ([denoteW], [iterB], [loop_stepB], [then_opt]) and its run
    ([trace]), with Lean's evaluator in place of [Denote.v]'s: [eval_term], [decide], [fail_exit]
    and the two marked exits are realized by the lane's [Lane_eval], over Lean's lowered
    [evalTerm], [Decision.decide], [errOf] and [Eval.badShape]/[Eval.outside]. The theorems of
    this development ([denoteD_approx], [denoteBD_same]) hold for any evaluator their statements
    fix, so the lane compares the trees, not two evaluators. Rocq strings become OCaml strings,
    and [nat] OCaml [int]. Rocq's [Z] is spelled as the program types spell a Lean natural, here
    OCaml [int]. These are assumptions of the extracted code, outside any proof here.
    An event's answer type crosses as [Obj.t], which [ocaml/STANDARDS.md] forbids in a program of
    the estate: the generated file is a test input, and its header says so. *)

From Stdlib Require Import List ZArith String Extraction.
Import ListNotations.
From Stdlib Require ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlNativeString.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Budget E4.BudgetDefs E4.Api E4.EffExtract.

Extract Inlined Constant RocqOfOCaml.Basics.int => "int".
Extract Inlined Constant RocqOfOCaml.RocqOfOCaml.int => "int".

Local Open Scope string_scope.

(** Lean's evaluator, realized by the lane's OCaml ([ocaml/engine/test/rocq/lane_eval.ml]). An
    exit is the lane's type, so the realizations can build one. *)
Extract Inductive exitv => "Lane_eval.exitv" ["Lane_eval.Success" "Lane_eval.Failure"].
Extract Constant eval_term => "Lane_eval.eval_term".
Extract Constant eval_terms => "Lane_eval.eval_terms".
Extract Constant decide => "Lane_eval.decide".
Extract Constant fail_exit => "Lane_eval.fail_exit".
Extract Constant bad_shape => "Lane_eval.bad_shape".
Extract Constant outside => "Lane_eval.outside".

(** The cells as a host function: an operation's name ("make", "get" or "set"), its cell or
    initial value, and the value a write stores. The lane answers it with Lean's own cell step,
    so the two runs it compares differ only where their trees do. *)
Definition cells_fn {C} (c : string -> val_ -> val_ -> C -> option (val_ * C)) : host StoreE C :=
  fun X e s =>
    match e in StoreE X return option (X * C) with
    | RefMake v => c "make" v Val_unit s
    | RefGet x => c "get" x Val_unit s
    | RefSet x w => c "set" x w s
    end.

(** The run at budget [k] of a program from the cells [cs] and the host state [s], each cell
    operation answered by [c] and each row by [f]: its steps, how it stopped, and the two states
    left. *)
Definition lane_run {C S} (c : string -> val_ -> val_ -> C -> option (val_ * C))
    (f : int -> val_ -> S -> option (exitv * S)) (k : nat) (e : eff native_op) (cs : C) (s : S) :=
  run_at k (route (cells_fn c) (fn_host f)) e (cs, s).

Extraction "rocq_run.ml" lane_run.
