import Effect4.Laws.Program.Typed.Commands.Clauses.All
import Effect4.Laws.Auto.Obligations
import Effect4.Program.Admission

/-!
# Laws.Program.Typed.AdmittedSource — from the API's admission to the typed state

The typed state's milestones range over lawful sources (`ProgramSource`, decisions row 114). The
API admits a program against an application's signature (`AdmittedProgram program app`,
`src/Effect4/Program/Admission.lean`), and admission runs the signature's own located refusal
(`admitSig`, decisions row 21's slice, step 2: the plan is
`docs/research/2026-10-04-claude-lead/sigapp-slice-plan.md`). So every admitted program denotes a
lawful source, with no premise.

* `lawfulSig_of_admitted` (proved): an admitted program's signature is lawful. It is the
  certificate's `signature` field read through `admitSig_ok_iff`.
* `AdmittedProgram.source` and `reachable_typed_admitted` (proved): the source an admitted
  program denotes, its rows and its declared services, and M6's consequence for it.
* `m7_admitted` (proved): at an empty row table, a program the API admits, with a closed
  requirement row and an answer-free tape, never goes wrong: M7a–c on its replay.

Placement (`AGENTS.md`). Concepts: `translation-simulation` (M7) and `residual-program-typing`
(admission). Claims: `m7-admitted` and `admitted-source-lawful`, in R9 and R1. Reach: any
`SigApp`, declared services included; for M7 the empty row table. The declared services reach
these statements only through tests until the slice's step 3 (`Author.build` builds at
`⟨table, []⟩`). It does not establish code generation at `app.signature` (step 4), M7 at a
non-empty row table (DI-57, R6), or structured service carriers (decisions row 118). It unlocks
R1's "every milestone statement takes the signature" for the API's admission, and M6 for every
admitted program with no premise.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **The bridge** (proved; claim `admitted-source-lawful`). An admitted program's signature is
lawful: admission ran `admitSig` (decisions row 21), and `admitSig_ok_iff` reads its `ok` as
`LawfulSig`. `E4-TYPED-CE-041`'s three witnesses, which the table-indexed admission admitted, are
refused now (`Test/Counterexamples/Program/AdmissionUnserved.lean`). -/
theorem lawfulSig_of_admitted {program : NativeEff} {app : SigApp}
    (a : AdmittedProgram program app) : LawfulSig app :=
  (admitSig_ok_iff app).mp a.signature

/-- The source an admitted program denotes: its rows and its declared services, lawful by the
bridge. -/
def _root_.Effect4.Program.AdmittedProgram.source {program : NativeEff} {app : SigApp}
    (a : AdmittedProgram program app) : ProgramSource :=
  { program, table := app.rows, services := app.services, lawful := lawfulSig_of_admitted a }

/-- **M6 for a program the API admits**, at any signature: every machine its admitted tapes reach
is typed. -/
theorem reachable_typed_admitted {program : NativeEff} {app : SigApp}
    (a : AdmittedProgram program app) (fuel : Nat) (tape : List Api.Decision)
    (admitted : AdmittedTape a.source a.ty fuel tape) :
    ∃ w, MachineTyped a.source a.ty w (replayR program fuel tape).machine :=
  reachable_typed a.source a.ty fuel a.typed tape admitted

/-- **M7 for a program the API admits** at an empty row table (R9 at the API's admission, within
`M7Fragment`): with a closed requirement row and an answer-free tape, its replay's exits fit, its
stores fit, and the frame machine has not halted. The services may be declared. -/
theorem m7_admitted {program : NativeEff} {app : SigApp} (a : AdmittedProgram program app)
    (emptyTable : app.rows = []) (fuel : Nat) (tape : List Api.Decision)
    (closedRow : a.ty.requires = Env.Requirement.empty)
    (answerFree : ∀ d ∈ tape, NoHostAnswer d) :
    M7Exits a.source a.ty fuel tape ∧ M7Stores a.source a.ty fuel tape ∧
      M7NoHalt a.source a.ty fuel tape :=
  have _fragment : M7Fragment a.source a.ty tape :=
    ⟨lawfulSig_of_admitted a, emptyTable, a.typed, closedRow, answerFree⟩
  m7_proved a.source a.ty fuel tape

end Effect4.Program.Typed
