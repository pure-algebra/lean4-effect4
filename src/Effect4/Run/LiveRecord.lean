import Effect4.Run.Live
import Effect4.Api.RunnerDerived

/-!
# Run.LiveRecord — a live session as versioned first-order data, and its restoration

Slice E of the authoring plan (`docs/research/2026-10-17-proof-scout/README.md` §7.5). A
`LiveRecord` captures a `Live` session's first-order fields: its format version, application,
program, session name, binding, budgets, journal and row spellings. No certificate is stored:
`LiveRecord.restore` checks the format version, reruns program admission at the record's
application, opens the admitted program with its row spellings, and replays the journal through
`Live.feedAll`.

* **Versioned record** (`currentVersion`, `Refusal.unsupportedVersion`): a record with an unknown
  format version is refused before admission.
* **Exact restoration** (`LiveRecord.restore_save`, `src/Effect4/Laws/Api/LiveRecord.lean`):
  keeping the row spellings beside the application and journal restores the exact `Run`.
* **Canonical bytes**: every field is first-order, so the record's codec is the generator's
  (`Canonical LiveRecord`, the Tool group, `src/Effect4/Tool/ToolDerived.lean`).

This file is no `module` file: it imports `Effect4.Run.Live`, an importer of the specialization
sites of decisions row 202.
-/

set_option autoImplicit false

namespace Effect4

open Effect4.Machine Effect4.Program Effect4.Store
open Effect4.Api.Runner (Command)

/-- The current format version of a saved live session record. -/
abbrev LiveRecord.currentVersion : Nat := 1

/-- **A live session as first-order data**: its format version, application, program, session name,
binding, budgets, journal and row spellings. No certificate is stored; restoration reruns admission. -/
structure LiveRecord where
  version : Nat := LiveRecord.currentVersion
  app : SigApp
  program : NativeEff
  session : String
  binding : String
  budget : Api.Budget
  journal : List Command
  rowNames : List (String × Nat)

namespace LiveRecord

/-- Why `LiveRecord.restore` refuses a saved record. -/
inductive Refusal
  /-- The record's format version is not `currentVersion`. -/
  | unsupportedVersion (version : Nat)
  /-- Program admission refused the record's program and application. -/
  | admission (why : AdmitRefusal)
deriving DecidableEq, Repr

/-- **Save a live session** as a `LiveRecord` at `currentVersion`. -/
def save (l : Live) : LiveRecord :=
  ⟨currentVersion, l.run.built.app, l.run.built.program, l.run.id, l.run.profile, l.run.budget,
    l.run.journal, l.run.built.rowNames⟩

/-- **Restore a live session** from a `LiveRecord`: check the format version, admit the program at
its application, open it with its row spellings, and replay the journal through the session's
checks (`Live.feedAll`). -/
def restore (r : LiveRecord) : Except Refusal Live :=
  if r.version ≠ currentVersion then
    .error (.unsupportedVersion r.version)
  else
    match Api.Built.ofProgram r.app r.program with
    | .error why => .error (.admission why)
    | .ok built =>
      .ok ((Live.open { built with rowNames := r.rowNames } r.session r.budget
        r.binding).feedAll (r.journal.map .wire))

end LiveRecord

end Effect4
