import Effect4.Run.LiveRecord
import Effect4.Tool.ToolDerived
import Effect4.Laws.Api.LiveRecord
import Effect4.Program.Authoring.ApplicationService
import Test.Dogfood.Scenario.Todo.Data

/-!
# Probe: a saved session over the object, and what a version field inside a record can see

Two questions.

1. `LiveRecord` (`src/Effect4/Run/LiveRecord.lean`) holds an application, a program and row
   names beside the session's own fields. Restated over the object, does `restore_save` keep its
   statement? It does exactly when the built program's row names are its signature's. With
   `Built.rowNames` a field, a hand-made value breaks it (the control below); with the names a
   projection of the signature, no premise is left.
2. A record's `version` field is read only after the whole record decodes. A later layout of the
   record (one more field) fails the generated decoder before any reader sees its version, so a
   version field cannot name the version of a changed layout. The object's node carries the layout
   as its spec instead (`probe-object.lean`).
-/

set_option autoImplicit false

namespace Probe.Record

open Effect4 Effect4.Program Effect4.Store Effect4.Api
open Effect4.Api.Runner (Command)

/-- The object: a program with its signature (`probe-object.lean` holds its codec). -/
structure Object where
  app : SigApp
  program : Eff NativeOp

/-- The spellings of the signature's rows, with their positions. -/
def rowNamesOf (app : SigApp) : List (String × Nat) :=
  app.rows.zipIdx.map fun (row, index) => (row.spelling, index)

/-- Forget the certificate. -/
def ofBuilt (b : Built) : Object := ⟨b.app, b.program⟩

/-- Decide admission. -/
def Object.open (o : Object) : Except AdmitRefusal Built := Built.ofProgram o.app o.program

theorem open_ofBuilt {b : Built} (h : b.rowNames = rowNamesOf b.app) :
    (ofBuilt b).open = .ok b := by
  unfold Object.open ofBuilt
  rw [Built.ofProgram_of_admitted b.app b.program b.admitted]
  cases b with
  | mk app program admitted rowNames =>
    dsimp only at h ⊢
    rw [h]
    rfl

/-- **A saved session over the object**: the object, then the session's own fields. The version is
the record's own (the Tool protocol's), unchanged. -/
structure Record where
  version : Nat := LiveRecord.currentVersion
  object : Object
  session : String
  binding : String
  budget : Budget
  journal : List Command

/-- Save a live session. -/
def save (l : Live) : Record :=
  { object := ofBuilt l.run.built, session := l.run.id, binding := l.run.profile,
    budget := l.run.budget, journal := l.run.journal }

/-- Restore: the version, then `open`, then the journal (`Live.feedAll`). -/
def restore (r : Record) : Except LiveRecord.Refusal Live :=
  if r.version ≠ LiveRecord.currentVersion then .error (.unsupportedVersion r.version)
  else match r.object.open with
    | .error why => .error (.admission why)
    | .ok built => .ok ((Live.open built r.session r.budget r.binding).feedAll (r.journal.map .wire))

/-- **`restore_save`, restated over the object**: its statement, with one premise, that the
session's row names are its signature's. -/
theorem restore_save (l : Live) (hn : l.run.built.rowNames = rowNamesOf l.run.built.app) :
    ∃ l', restore (save l) = .ok l' ∧ l'.run = l.run := by
  refine ⟨(Live.open l.run.built l.run.id l.run.budget l.run.profile).feedAll
    (l.run.journal.map .wire), ?_, ?_⟩
  · unfold restore save
    dsimp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [open_ofBuilt hn]
    rfl
  · rw [Live.feedAll_wire]
    exact Live.journal_replays l

/-! ## The to-do -/

/-- The to-do's service, built as `Compiler.check` builds it. -/
def todoBuilt : Option Built :=
  match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
  | .ok m => (Author.build m).toOption
  | .error _ => none

-- finite evaluation: the to-do's session restores through the object to the same journal and the
-- same names
#guard (todoBuilt.map fun b =>
  let l := Live.open b "todo"
  match restore (save l) with
  | .ok l' => l'.run.journal == l.run.journal && l'.run.built.rowNames == l.run.built.rowNames
  | .error _ => false) = some true

-- control: a session opened from a hand-made value whose names are not its signature's does not
-- come back with those names: the premise of `restore_save` is needed while `Built.rowNames` is a
-- field (the value `Test/Program/RunAdmissionControls.lean` writes on purpose)
#guard (todoBuilt.map fun b =>
  let l := Live.open { b with rowNames := [("stored", 9)] } "todo"
  match restore (save l) with
  | .ok l' => l'.run.built.rowNames == [("stored", 9)]
  | .error _ => true) = some false

/-! ## What a version field inside a record can see -/

/-- The to-do's session record, at a version this reader does not know. -/
def todoRecord (version : Nat) : Option LiveRecord :=
  todoBuilt.map fun b => { LiveRecord.save (Live.open b "todo") with version }

-- control: at the same layout, the version field refuses as it should
#guard (todoRecord 2).map (fun r => match LiveRecord.restore r with
  | .error (.unsupportedVersion 2) => true
  | _ => false) = some true

-- control: a later layout (one more field) is refused by the generated decoder before any reader
-- sees its version: the version field cannot name it
#guard (todoRecord 2).map (fun r =>
  let v2 : Store.Val := match Canonical.toVal r with
    | .ctor 0 args => .ctor 0 (args ++ [.nat 0])
    | v => v
  (Canonical.ofVal (α := LiveRecord) v2).isNone &&
    (Canonical.decode (α := LiveRecord) (Store.Val.encode v2)).isNone) = some true

end Probe.Record
