import Effect4.Program.Typing.Splice
import Effect4.Program.Typing.PartsTable

/-!
# Program.Edit — the edit session: a sketch, its address table, and edits fed one at a time

**The question.** A tool that edits a program shows its address table after every edit. Checking
the whole program again at each edit costs the whole program. The edit session keeps the table
beside the sketch, and an edit that keeps its focus's type splices the table instead
(`Table.splice`): it checks the new sub-program and nothing else.

The session holds a sketch (`Program/Sketch.lean`): a whole program, definition block included,
with its hole table. A program with no hole is a sketch with an empty hole table. Holes keep an
incomplete program typed, so filling a hole at its declared type stays on the spliced path.

## The face

The face is the session API's (decisions rows 326 and 334): `open`, `feed` and `view`, with an
edit as one kind of event. A run of edits is the fold of `feed` (`run`).

| Operation | It takes | It answers |
| --- | --- | --- |
| `EditSession.open` | an application and a sketch | the session, with the sketch's table, part by part (`Sketch.annotate`) |
| `EditSession.feed` | a session and an edit | the next session, and what the edit did to the table (`Edit.Delta`) |
| `EditSession.run` | a session and a list of edits | the session after each edit in turn |
| `EditSession.view` | a session | the table, its refusals, and the sketch's type |
| `EditSession.feedStep` | a session and an edit | `feed`'s answer, and the journal's step: the edit, the sub-program it replaced, the delta |

## What `feed` does

An edit `fill a q` puts `q` in place of the sub-program at the address `a` (`Sketch.fillAt`). An
edit `omitAt a row` declares a hole with the row, and puts the hole in that place (`Sketch.omitAt`).
For a fill, the session reads the old focus from its own table (`Table.typedAt`), not from the
sketch:

- **spliced**: the address is below the root, the table types the root and the address, and the
  checker gives `q` the old sub-program's type in its environment, at the signature of the part
  that holds the address (`Sketch.sigAt`). The table is spliced, and the new subtree's addresses
  are the addresses to show again.
- **rechecked**: any other edit of a program. The table is computed again, part by part.

An omission splices too, below the root, where the table types the root and the address and the
hole row declares exactly the focus's type, with closed, normal and formed columns: the hole's
one entry replaces the subtree's segment (`Sketch.table_omit`). A typed sketch's table stays under
a grown hole table (`Sketch.table_more_holes`), so the grown signature changes no other entry.
- **unchanged**: the address holds no program. Nothing changes.

The session's invariant is that its table is its sketch's table (`EditSession.Coherent`). The open
makes it, and each edit keeps it (`EditSession.run_coherent`, `Laws/Program/Edit.lean`). The claim
`edit-session-coherent` points at what that gives: the view is the checker's answer
(`EditSession.reached_view`). The splice over a whole program's parts gives the spliced case
(`Sketch.table_fill`).

## What this module is not

- It runs nothing. Running and editing share the face; one event type for both is open.
- It counts no cost. The cost is read off the definitions, and no theorem counts it.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **An edit**: one event of an edit session. -/
inductive Edit where
  /-- put the program in place of the sub-program at the address -/
  | fill (path : List Nat) (program : NativeEff)
  /-- declare a hole with the row, and put it in place of the sub-program at the address -/
  | omitAt (path : List Nat) (row : Row)

/-- **What an edit did to the address table.** -/
inductive Edit.Delta where
  /-- the address holds no program, and nothing changed -/
  | unchanged
  /-- the edit kept its focus's type: the table is spliced, and these addresses are new. An
  address of the old subtree that the new one lacks is gone and is not listed: a view replaces
  the whole subtree at the edited address. -/
  | spliced (shown : List (List Nat))
  /-- the table is computed again -/
  | rechecked
  deriving DecidableEq, Repr

/-- **The environment and the type that a table holds at an address**: at the first entry at the
address, where it holds an environment of variables and a type. On a sketch's table it is the
focus there (`Table.typedAt_table`, `Laws/Program/Edit.lean`). -/
def Table.typedAt (t : List Table.Entry) (a : List Nat) : Option (TyEnv × EffTy) :=
  match t.find? (fun e => decide (e.path = a)) with
  | some ⟨_, some (.env tys), some (.ok ty)⟩ => some (tys, ty)
  | _ => none

/-- **An edit session**: an application, a sketch over it, and the sketch's address table. -/
structure EditSession where
  /-- the application the sketch is checked against -/
  app : SigApp
  /-- the sketch: a whole program and its hole table -/
  sketch : Sketch
  /-- the address table the session keeps; its sketch's table (`EditSession.Coherent`) -/
  table : List Table.Entry

namespace EditSession

/-- **The session's invariant**: its table is its sketch's table. -/
def Coherent (l : EditSession) : Prop := l.table = l.sketch.table l.app

/-- **Open** a session on a sketch: its table, part by part (`Sketch.annotate`). -/
def «open» (app : SigApp) (s : Sketch) : EditSession := ⟨app, s, s.annotate app⟩

/-- **Feed** one edit: the next session, and what the edit did to the table. -/
def feed (l : EditSession) : Edit → EditSession × Edit.Delta
  | .fill a q =>
    match l.sketch.fillAt a q with
    | some s' =>
      -- deferred: Lean evaluates a `let` before the match, and only a branch that checks again
      -- may pay for the whole table (Codex's overwatch, EDIT-OW-01)
      let rechecked : Unit → EditSession × Edit.Delta := fun _ =>
        ({ l with sketch := s', table := s'.annotate l.app }, .rechecked)
      match a, Table.typedAt l.table [], Table.typedAt l.table a with
      | _ :: _, some _, some (tys, ty) =>
        match Annotate.check (l.sketch.sigAt l.app a) tys a q with
        | (sub, .ok ty') =>
          if ty' = ty then
            ({ l with sketch := s', table := Table.splice l.table a sub },
              .spliced (sub.map (·.path)))
          else rechecked ()
        | (_, .error _) => rechecked ()
      | _, _, _ => rechecked ()
    | none => (l, .unchanged)
  | .omitAt a row =>
    match l.sketch.omitAt l.app a row with
    | some s' =>
      -- deferred: Lean evaluates a `let` before the match, and only a branch that checks again
      -- may pay for the whole table (Codex's overwatch, EDIT-OW-01)
      let rechecked : Unit → EditSession × Edit.Delta := fun _ =>
        ({ l with sketch := s', table := s'.annotate l.app }, .rechecked)
      match a, Table.typedAt l.table [], Table.typedAt l.table a with
      | _ :: _, some _, some (tys, ty) =>
        if row = Row.hole row.name ty.answer ty.error ty.requires.elems ∧
            ty.answer.closed = true ∧ ty.error.closed = true ∧
            ty.answer.normalize = ty.answer ∧ ty.error.normalize = ty.error ∧
            (Formation.check (Formation.instantiatedSites row.normalizeTypes [])).isNone = true then
          let entry : Table.Entry := ⟨a, some (.env tys), some (.ok ty)⟩
          ({ l with sketch := s', table := Table.splice l.table a [entry] }, .spliced [a])
        else rechecked ()
      | _, _, _ => rechecked ()
    | none => (l, .unchanged)

/-- **The address an edit acts at.** -/
def _root_.Effect4.Program.Edit.path : Edit → List Nat
  | .fill a _ => a
  | .omitAt a _ => a

/-- **One step of the journal**: the edit, the sub-program it replaced, and what it did to the
table. The replaced sub-program is what an undo puts back (`EditSession.feed_undo`). -/
structure _root_.Effect4.Program.Edit.Step where
  /-- the edit -/
  edit : Edit
  /-- the sub-program at the edit's address before the edit, where the address held one -/
  replaced : Option NativeEff
  /-- what the edit did to the table -/
  delta : Edit.Delta

/-- **Feed one edit and record it**: the next session, and the journal's step. -/
def feedStep (l : EditSession) (e : Edit) : EditSession × Edit.Step :=
  let replaced := match (Node.eff l.sketch.program).at_ e.path with
    | some (.eff q) => some q
    | _ => none
  let (l', delta) := l.feed e
  (l', ⟨e, replaced, delta⟩)

/-- **A run of edits**: the fold of `feed`. -/
def run (l : EditSession) (edits : List Edit) : EditSession :=
  edits.foldl (fun l e => (l.feed e).1) l

/-- **What a session shows**: its table, the distinct refusals of its entries in the table's
order, and the type its table holds at the root. -/
structure View where
  /-- the address table -/
  table : List Table.Entry
  /-- the distinct refusals of the entries, in the table's order -/
  refusals : List TypeRefusal
  /-- the sketch's type, where the table holds one at the root -/
  type : Option EffTy

/-- **View** a session. On a coherent session the refusals are the sketch's (`Sketch.refusals`),
and the type is its check's (`EditSession.view_type`, `Laws/Program/Edit.lean`). -/
def view (l : EditSession) : View :=
  ⟨l.table, (l.table.filterMap fun e => e.result.bind Checker.refusal).eraseDups,
    (Table.typedAt l.table []).map (·.2)⟩

end EditSession

end Effect4.Program
