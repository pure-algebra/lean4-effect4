import Effect4.Laws.Program.Typed.Commands.Clauses.All
import Effect4.Laws.Program.Typed.AdmissionRows
import Effect4.Laws.Auto.Obligations

/-!
# Laws.Program.Typed.AdmittedSource — from the API's admission to the typed state

The typed state's milestones range over lawful sources (`ProgramSource`, decisions row 114). The
API admits a program against a row table (`AdmittedProgram`, `src/Effect4/Program/Admission.lean`).
No theorem connected the two. This module is the first step of decisions row 21's slice, which
threads the application's signature through admission (the plan:
`docs/research/2026-10-04-claude-lead/sigapp-slice-plan.md`).

* `m7_admitted` (proved): at the empty row table, a program the API admits, with a closed
  requirement row and an answer-free tape, never goes wrong: M7a–c on its replay.
* `AdmissionGap`: the three conditions `LawfulSig` asks of a row table that the API's admission
  does not check: every required key served, every row well scoped, every template admissible
  (`E4-TYPED-CE-041` witnesses each).
* `lawfulSig_of_admitted` (proved): an admitted table that meets the gap is a lawful signature
  with the built-in services. Every other row condition is admission's own, read by row in
  `Laws/Program/Typed/AdmissionRows.lean`.
* `AdmittedProgram.source` and `reachable_typed_admitted` (proved): the source such an admitted
  program denotes, and M6's consequence for it.

Placement (`AGENTS.md`). Concepts: `translation-simulation` (M7) and `residual-program-typing`
(admission). Claims: `m7-admitted` and `admitted-source-lawful`, in R9 and R1. Reach: the built-in
services only (no service declarations), and for M7 the empty row table. It does not establish
admission at an application's own services (`SigApp` with declarations), which is the slice's
second step, nor M7 at a non-empty row table (DI-57, R6). It unlocks R1's "every milestone
statement takes the signature" for the API's admission.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **M7 for a program the API admits** at the empty row table (R9 at the API's admission): with a
closed requirement row and an answer-free tape, its replay's exits fit, its stores fit, and the
frame machine has not halted. -/
theorem m7_admitted {program : NativeEff} (a : AdmittedProgram program []) (fuel : Nat)
    (tape : List Api.Decision) (closedRow : a.ty.requires = Env.Requirement.empty)
    (answerFree : ∀ d ∈ tape, NoHostAnswer d) :
    M7Exits { program } a.ty fuel tape ∧ M7Stores { program } a.ty fuel tape ∧
      M7NoHalt { program } a.ty fuel tape :=
  have _fragment : M7Fragment { program } a.ty tape :=
    ⟨SigApp.lawful_empty, rfl, a.typed, closedRow, answerFree⟩
  m7_proved { program } a.ty fuel tape

/-- **The admission gap**: what `LawfulSig` asks of a row table and the API's admission does not
check (`E4-TYPED-CE-041` witnesses each clause). Decisions row 21's slice, step 2, moves the three
checks into admission, and the gap closes. -/
structure AdmissionGap (table : RowTable) : Prop where
  /-- Every key a row requires has a carrier at the built-in services. -/
  served : ∀ r ∈ table, ∀ k ∈ r.requires, ((SigApp.mk table []).serviceTy k).isSome = true
  /-- Every parameter a row's answer or error mentions is one its request binds. -/
  wellScoped : ∀ r ∈ table, r.wellScoped = true
  /-- No parameter of a row's columns sits under a union head. -/
  templates : ∀ r ∈ table,
    r.request.templateAdmissible = true ∧ r.answer.templateAdmissible = true ∧
      r.error.templateAdmissible = true

/-- **The bridge, row-table half** (proved; claim `admitted-source-lawful`). An admitted table that
meets the admission gap is a lawful signature with the built-in services. The gap gives four of
`rowChecks`' sixteen checks and `served`. Admission's fields give the other twelve, read by row
(`Laws/Program/Typed/AdmissionRows.lean`), and its key check is `rowsDistinct`. With no declaration,
`services` and `codesDistinct` hold vacuously. -/
theorem lawfulSig_of_admitted {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) (gap : AdmissionGap table) :
    LawfulSig (SigApp.mk table []) := by
  obtain ⟨keys, collision, trailing⟩ := (Table.lawful_eq_true_iff table).mp a.lawful
  have runnable := (checkTable_eq_none_iff table).mp a.runnable
  have ints := (findIntInTable_eq_none_iff table).mp a.intFreeTable
  have handles := (findInternalHandleInTable_eq_none_iff table).mp a.internalFreeTable
  have filled := (findEmptyColumnInTable_eq_none_iff table).mp a.columnsTable
  obtain ⟨served, scopedRows, templates⟩ := gap
  refine ⟨fun r hr => ?_, List.pairwise_map.mp keys, fun _ h => (nomatch h), List.Pairwise.nil,
    served⟩
  aesop (add norm simp [rowChecks])

/-- The source an admitted program over a table that meets the gap denotes. -/
def _root_.Effect4.Program.AdmittedProgram.source {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) (gap : AdmissionGap table) : ProgramSource :=
  { program, table, lawful := lawfulSig_of_admitted a gap }

/-- **M6 for a program the API admits** over a table that meets the gap: every machine its
admitted tapes reach is typed. -/
theorem reachable_typed_admitted {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) (gap : AdmissionGap table) (fuel : Nat)
    (tape : List Api.Decision) (admitted : AdmittedTape (a.source gap) a.ty fuel tape) :
    ∃ w, MachineTyped (a.source gap) a.ty w (replayR program fuel tape).machine :=
  reachable_typed (a.source gap) a.ty fuel a.typed tape admitted

end Effect4.Program.Typed
