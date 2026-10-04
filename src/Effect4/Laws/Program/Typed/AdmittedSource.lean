import Effect4.Laws.Program.Typed.Commands.Clauses.All
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
* `lawfulSig_of_admitted` (a planned goal): an admitted table whose required keys are served is a
  lawful signature with the built-in services. The served premise is not redundant: the API's
  admission does not check it (`E4-TYPED-CE-041`).
* `AdmittedProgram.source` and `reachable_typed_admitted` (proved modulo that goal): the source an
  admitted program over a served table denotes, and M6's consequence for it.

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

/-- Every key a table's rows require has a carrier at the built-in services. The API's admission
does not check it (`E4-TYPED-CE-041`). -/
def TableServed (table : RowTable) : Prop :=
  ∀ r ∈ table, ∀ k ∈ r.requires, ((SigApp.mk table []).serviceTy k).isSome = true

/-- **The bridge, row-table half** (planned goal; claim `admitted-source-lawful`). An admitted table
whose required keys are served is a lawful signature with the built-in services: admission's row
checks are `rowChecks`, and its key check is `rowsDistinct`. -/
proof_goal lawfulSig_of_admitted {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) (served : TableServed table) :
    LawfulSig (SigApp.mk table [])

/-- The source an admitted program over a served table denotes. -/
def _root_.Effect4.Program.AdmittedProgram.source {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) (served : TableServed table) : ProgramSource :=
  { program, table, lawful := lawfulSig_of_admitted a served }

/-- **M6 for a program the API admits** over a served table: every machine its admitted tapes
reach is typed. -/
theorem reachable_typed_admitted {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) (served : TableServed table) (fuel : Nat)
    (tape : List Api.Decision) (admitted : AdmittedTape (a.source served) a.ty fuel tape) :
    ∃ w, MachineTyped (a.source served) a.ty w (replayR program fuel tape).machine :=
  reachable_typed (a.source served) a.ty fuel a.typed tape admitted

end Effect4.Program.Typed
