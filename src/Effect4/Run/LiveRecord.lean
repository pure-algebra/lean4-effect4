import Effect4.Run.Live
import Effect4.Api.Object
import Effect4.Api.RunnerDerived

/-!
# Run.LiveRecord — a live session as versioned first-order data, and its restoration

Slice E of the authoring plan (`docs/research/2026-10-17-proof-scout/README.md` §7.5). A
`LiveRecord` holds the program object and the session's version, name, binding, budgets and journal.
No certificate is stored. `LiveRecord.restore` checks the version and opens the object through
program admission. It then replays the journal through `Live.feedAll`.

* **Versioned record** (`currentVersion`, `Refusal.unsupportedVersion`): a record with an unknown
  format version is refused before admission.
* **Exact restoration** (`LiveRecord.restore_save`, `src/Effect4/Laws/Api/LiveRecord.lean`):
  the object and journal restore the exact `Run`.
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

/-- A saved session: its version, program object, name, binding, budgets and journal.
Restoration recomputes admission; no certificate is stored. -/
structure LiveRecord where
  version : Nat := LiveRecord.currentVersion
  object : Object
  session : String
  binding : String
  budget : Api.Budget
  journal : List Command

namespace LiveRecord

/-- Why `LiveRecord.restore` refuses a saved record. -/
inductive Refusal
  /-- The record's format version is not `currentVersion`. -/
  | unsupportedVersion (version : Nat)
  /-- Program admission refused the record's program and application. -/
  | admission (why : AdmitRefusal)
deriving DecidableEq

/-- **Save a live session** as a `LiveRecord` at `currentVersion`. -/
def save (l : Live) : LiveRecord :=
  ⟨currentVersion, Object.ofBuilt l.run.built, l.run.id, l.run.profile, l.run.budget,
    l.run.journal⟩

/-- Restore a saved session: check its version, open its program object, and replay the journal
through the session's checks (`Live.feedAll`). -/
def restore (r : LiveRecord) : Except Refusal Live :=
  if r.version ≠ currentVersion then
    .error (.unsupportedVersion r.version)
  else
    match r.object.open with
    | .error why => .error (.admission why)
    | .ok built =>
      .ok ((Live.open built r.session r.budget r.binding).feedAll (r.journal.map .wire))

end LiveRecord

end Effect4
