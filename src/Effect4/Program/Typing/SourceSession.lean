import Effect4.Program.Typing.Source
import Effect4.Program.Edit

/-!
# Program.Typing.SourceSession — the edit session of a sketch as written, at an application

**The question.** An edit session (`EditSession`, `Program/Edit.lean`) keeps a sketch with its
address table. Its table reads the program as written, so a layer reference is refused there.
An agent edits the program as written: the references stay, so two uses of one layer keep one
memo key at run time. This module keeps the sketch as written beside the edit session of its
expansion, and shows that session's table at the source's addresses (`Table.atSource`,
`Program/Typing/Source.lean`). Decisions row 373 (7) rules the route.

## The face

| Operation | It takes | It answers |
| --- | --- | --- |
| `SourceSession.open` | an application and a sketch | the sketch, and the edit session of its expansion |
| `SourceSession.feed` | a session and an edit | the next session, and what the edit did to the table |
| `SourceSession.view` | a session | the table at the source's addresses, its refusals and the type through the references |
| `SourceSession.focusAt` | a session and an address | the sub-program as written, with the environment and the type that the table holds there |

## What `feed` does

The edit applies to the sketch as written (`Sketch.edit`). Its expansion is computed again, and
it is compared with the expansion's own edit at the same address (`Edit.expanded`):

- **the expansion moved only at the address**: the edit session of the expansion takes that edit,
  and its own law decides whether the table splices (`EditSession.feed`);
- **any other expansion**: an edit inside a referenced layer moves every copy of it, or an edit
  changed a reference. The edit session of the new expansion opens again.

The comparison costs a traversal of the program, and no check. The session's invariant is
`SourceSession.Coherent`, and each edit keeps it (`Laws/Program/SourceTable.lean`).

## What this module is not

- It runs nothing. A run of a program with references redirects each reference to its target.
- It counts no cost. The cost is read off the definitions, and no theorem counts it.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **The sketch after an edit**: a filling (`Sketch.fillAt`) or an omission (`Sketch.omitAt`).
`none` where the address holds no program. -/
def Sketch.edit (s : Sketch) (app : SigApp) : Edit → Option Sketch
  | .fill a q => s.fillAt a q
  | .omitAt a row => s.omitAt app a row

/-- **The edit of an expansion at the same address**: a filling by the new expansion's
sub-program there, and an omission as it is. `none` where the new expansion holds no program at
the address. -/
def Edit.expanded (x : Sketch) : Edit → Option Edit
  | .fill a _ =>
    match (Node.eff x.program).at_ a with
    | some (.eff q) => some (.fill a q)
    | _ => none
  | .omitAt a row => some (.omitAt a row)

/-- **What a delta shows, at the source's addresses**: the addresses of a copy are dropped. -/
def Edit.Delta.atSource (sites : List (List Nat)) : Edit.Delta → Edit.Delta
  | .spliced shown => .spliced (shown.filter fun a => !Table.belowSite sites a)
  | d => d

/-- **The edit session of a sketch as written**: the sketch, and the edit session of its
expansion. Its invariant is `SourceSession.Coherent`. -/
structure SourceSession where
  /-- the sketch as written: its program keeps its layer references -/
  sketch : Sketch
  /-- the edit session of the sketch's expansion, at the application -/
  expanded : EditSession

namespace SourceSession

/-- The application the sketch is checked against. -/
def app (l : SourceSession) : SigApp := l.expanded.app

/-- **The session's invariant**: the edit session holds the sketch's expansion, and it is
coherent. -/
def Coherent (l : SourceSession) : Prop :=
  l.expanded.sketch = l.sketch.expand ∧ l.expanded.Coherent

/-- **Open** a session on a sketch: the edit session of its expansion. -/
def «open» (app : SigApp) (s : Sketch) : SourceSession := ⟨s, EditSession.open app s.expand⟩

/-- **Feed** one edit: the next session, and what the edit did to the table, at the source's
addresses. -/
def feed (l : SourceSession) (e : Edit) : SourceSession × Edit.Delta :=
  match l.sketch.edit l.app e with
  | none => (l, .unchanged)
  | some s' =>
    let x := s'.expand
    -- deferred: only the branch that opens again pays for the whole table
    let reopened : Unit → SourceSession × Edit.Delta := fun _ =>
      (⟨s', EditSession.open l.app x⟩, .rechecked)
    match Edit.expanded x e with
    | some e' =>
      if (l.expanded.sketch.edit l.app e').map (fun y => (y.program, y.holes)) =
          some (x.program, x.holes) then
        let (ex, d) := l.expanded.feed e'
        (⟨s', ex⟩, d.atSource s'.sites)
      else reopened ()
    | none => reopened ()

/-- **Feed one edit and record it**: the next session, and the journal's step. The replaced
sub-program is the one as written, which an undo puts back. -/
def feedStep (l : SourceSession) (e : Edit) : SourceSession × Edit.Step :=
  let replaced := match (Node.eff l.sketch.program).at_ e.path with
    | some (.eff q) => some q
    | _ => none
  let (l', delta) := l.feed e
  (l', ⟨e, replaced, delta⟩)

/-- **A run of edits**: the fold of `feed`. -/
def run (l : SourceSession) (edits : List Edit) : SourceSession :=
  edits.foldl (fun l e => (l.feed e).1) l

/-- **The table at the source's addresses**: the expansion's table, its copies dropped, its root
replaced by an ill-formed reference's refusal. -/
def table (l : SourceSession) : List Table.Entry :=
  Table.atSource l.sketch.sites l.sketch.program.firstRefFault l.expanded.table

/-- **What the session shows, as an edit session**: the application, the sketch as written, and
the table at the source's addresses. A view of an edit session draws it. -/
def shown (l : SourceSession) : EditSession := ⟨l.app, l.sketch, l.table⟩

/-- **View** a session: its table at the source's addresses, the table's distinct refusals, and
the type through the references (`SourceSession.reached_view`). -/
def view (l : SourceSession) : EditSession.View := l.shown.view

/-- **The focus at a source address**: the sub-program as written, with the environment and the
type that the table holds there. Below the root they are the expansion's focus there
(`SourceSession.focusAt_typed`). -/
def focusAt (l : SourceSession) (a : List Nat) : Option (Focus NativeOp) :=
  match (Node.eff l.sketch.program).at_ a, Table.typedAt l.table a with
  | some (.eff q), some (tys, ty) => some ⟨q, tys, ty⟩
  | _, _ => none

end SourceSession

end Effect4.Program
