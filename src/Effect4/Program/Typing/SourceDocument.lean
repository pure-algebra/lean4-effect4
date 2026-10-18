import Effect4.Program.Typing.SourceSession

/-!
# Program.Typing.SourceDocument — document identity, context inspection and atomic checked edits

An edit session (`SourceSession`, `Program/Typing/SourceSession.lean`) keeps a sketch as written
with the edit session of its expansion. Its `feed` operation is a draft operation: an ill-typed
edit still updates the session and records its refusals in the table.

`Doc` wraps `SourceSession` with a document identity (`DocId`: a name and an opening generation)
and a monotonically advancing `revision : Nat`:

* `Doc.inspect` answers, at a source address that holds a program, an `EditTarget` (`doc`,
  `revision`, `path`, `expected`), the typed focus (`SourceSession.focusAt`), the address-table
  entry, and any located refusal there.
* `Doc.commit` validates the target's document identity (`Refusal.foreign`), the revision
  (`Refusal.stale`), and the sub-program at the address (`Refusal.moved`), then computes the
  candidate session once and checks that the candidate source has a type (`Refusal.refused`). Under
  `Policy.keepExactType`, it also checks that the root type and the focus's environment and type at
  the target address are unchanged (`Refusal.typeChanged`, `Refusal.localChanged`). A refusal
  returns no document, so the caller keeps the old one.
* `Doc.draft` applies an unchecked edit (`SourceSession.feedStep`) and advances `revision`.
* `Doc.undo` restores a replaced sub-program at a new revision (`revision + 1`), so revisions only
  grow and targets taken before `undo` refuse as `stale`.
* `Doc.fork` produces a copy of the document with a new `DocId`.

The soundness theorem `Doc.commit_sound` lives in `Laws/Program/SourceDocument.lean`.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- A document's identity: a name and an opening generation allocated by the session owner. -/
structure DocId where
  name : String := "default"
  generation : Nat := 0
deriving DecidableEq, Repr

/-- A versioned source document: its identity, its source session, and its revision counter. -/
structure Doc where
  id : DocId := {}
  session : SourceSession
  revision : Nat := 0

/-- Open a document at revision zero. -/
def Doc.open (app : SigApp) (s : Sketch) (id : DocId := {}) : Doc :=
  ⟨id, SourceSession.open app s, 0⟩

/-- An edit target: the document identity and revision it was read at, the source address, and the
sub-program as written that the address held then. -/
structure EditTarget where
  doc : DocId := {}
  revision : Nat
  path : List Nat
  expected : NativeEff
deriving DecidableEq

/-- What an atomic edit does at its target. -/
inductive Change
  /-- put the program at the address -/
  | fill (q : NativeEff)
  /-- declare a hole with the focus's type and put it at the address -/
  | omitHole (name : String)
deriving DecidableEq

/-- The validation policy of `Doc.commit`. -/
inductive Policy
  | keepExactType
  | recheckSource
deriving DecidableEq, Repr

/-- Why an atomic edit is refused. -/
inductive Doc.Refusal
  /-- the target belongs to another document or generation; the receiving document's identity is
  given -/
  | foreign (expected : DocId)
  /-- the target was read at another revision; the current one is given -/
  | stale (current : Nat)
  /-- the address no longer holds the expected sub-program -/
  | moved
  /-- an omission at an address with no typed focus -/
  | noFocus
  /-- the candidate source has no type: its refusals, the first one the check's -/
  | refused (why : List TypeRefusal)
  /-- `keepExactType`: the root type would change -/
  | typeChanged (old : Option EffTy) (new : EffTy)
  /-- `keepExactType`: the focus's environment or type would change -/
  | localChanged (old new : Option (TyEnv × EffTy))
deriving DecidableEq

/-- Short tag of a `Doc.Refusal`. -/
def Doc.Refusal.reason : Doc.Refusal → String
  | .foreign _ => "foreign"
  | .stale _ => "stale"
  | .moved => "moved"
  | .noFocus => "noFocus"
  | .refused _ => "refused"
  | .typeChanged _ _ => "typeChanged"
  | .localChanged _ _ => "localChanged"

/-- What `Doc.inspect` answers at an address that holds a program. -/
structure Doc.Inspection where
  target : EditTarget
  focus : Option (Focus NativeOp)
  entry : Option Table.Entry
  refusal : Option TypeRefusal

/-- The target that `inspect` hands out: the document identity, the current revision, the address
and its sub-program as written, where the address holds one. -/
def Doc.target (d : Doc) (path : List Nat) : Option EditTarget :=
  match (Node.eff d.session.sketch.program).at_ path with
  | some (.eff q) => some ⟨d.id, d.revision, path, q⟩
  | _ => none

/-- **Inspect** a source address: its edit target, its typed focus (`SourceSession.focusAt`), its
table entry, and any located refusal at that entry. `none` where the address holds no program. -/
def Doc.inspect (d : Doc) (path : List Nat) : Option Doc.Inspection :=
  (d.target path).map fun target =>
    let entry := d.session.table.find? fun e => decide (e.path = path)
    let refusal := entry.bind fun e => e.result.bind Checker.refusal
    ⟨target, d.session.focusAt path, entry, refusal⟩

/-- The edit a change makes at a target. -/
def Doc.editOf (d : Doc) (t : EditTarget) : Change → Option Edit
  | .fill q => some (.fill t.path q)
  | .omitHole name => (d.session.focusAt t.path).map fun f =>
    .omitAt t.path (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems)

/-- The candidate session after an edit. -/
def Doc.after (d : Doc) (e : Edit) : SourceSession := (d.session.feed e).1

/-- **Atomic checked edit.** Validates document identity, revision, expected sub-program, and the
candidate view's type under `policy`, binding the candidate session and its view once. -/
def Doc.commit (d : Doc) (t : EditTarget) (c : Change) (policy : Policy := .keepExactType) :
    Except Doc.Refusal Doc :=
  if t.doc ≠ d.id then .error (.foreign d.id)
  else if t.revision ≠ d.revision then .error (.stale d.revision)
  else if (Node.eff d.session.sketch.program).at_ t.path ≠ some (.eff t.expected) then .error .moved
  else
    match d.editOf t c with
    | none => .error .noFocus
    | some e =>
      let next := d.after e
      let view := next.view
      match view.type with
      | none => .error (.refused view.refusals)
      | some T' =>
        match policy with
        | .recheckSource => .ok ⟨d.id, next, d.revision + 1⟩
        | .keepExactType =>
          if d.session.view.type ≠ some T' then .error (.typeChanged d.session.view.type T')
          else if Table.typedAt next.table t.path ≠ Table.typedAt d.session.table t.path
          then .error (.localChanged (Table.typedAt d.session.table t.path)
            (Table.typedAt next.table t.path))
          else .ok ⟨d.id, next, d.revision + 1⟩

/-- **Draft edit**: applies an unchecked edit (`SourceSession.feedStep`) and advances `revision`. -/
def Doc.draft (d : Doc) (e : Edit) : Doc × Edit.Step :=
  let (s', step) := d.session.feedStep e
  (⟨d.id, s', d.revision + 1⟩, step)

/-- **Undo** a previous edit by restoring `old` at `path` at a new revision (`d.revision + 1`), so
revisions never repeat. -/
def Doc.undo (d : Doc) (path : List Nat) (old : NativeEff) : Doc × Edit.Step :=
  d.draft (.fill path old)

/-- **Fork** a document under a fresh `DocId`. -/
def Doc.fork (d : Doc) (id : DocId) : Doc :=
  { d with id }

end Effect4.Program
