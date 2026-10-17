(** * BudgetExtract: the budgeted runner as OCaml, for fast frames

    Extracts [Api.run_at], [Api.settle] and [Api.frames] with their hosts, the examples and two
    requests of the to-do fixture, so an
    OCaml driver ([gen/budget_view.ml]) computes the frames of a run and writes them for the view.
    The program types are the estate's own ([EffExtract], generated from
    [ocaml/eff/eff_types.ml]); [nat] and [Z] become OCaml [int] and Rocq strings OCaml strings,
    assumptions of the extracted code outside any proof here, as in [Extract.v]. An event's
    answer type crosses as [Obj.t], which [ocaml/STANDARDS.md] forbids in the estate, so the code
    stays in this folder. *)

From Stdlib Require Import List ZArith Extraction.
From Stdlib Require ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlNativeString.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Budget E4.BudgetDefs E4.Api E4.Examples E4.EffExtract.
Require E4.Todo_fixture E4.TodoCheck.

Extract Inlined Constant RocqOfOCaml.Basics.int => "int".
Extract Inlined Constant RocqOfOCaml.RocqOfOCaml.int => "int".

Extraction "budget_run.ml" run_at settle frames route cells_host tape fn_host Author.ready
  doubling forever ping cell_counter before_edit after_edit doubling_rec self_call twice units by_tape by_unit
  E4.TodoCheck.tape_of E4.Todo_fixture.program_0 E4.Todo_fixture.calls_0 E4.Todo_fixture.program_2
  E4.Todo_fixture.calls_2.
