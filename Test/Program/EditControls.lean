import Effect4.Laws.Program.Edit
import Test.Program.SpliceControls
import Test.Program.PartsControls

/-!
Readers and finite evaluations of the edit session (`src/Effect4/Program/Edit.lean`, its laws
`src/Effect4/Laws/Program/Edit.lean`, the claims `edit-session-coherent`, `edit-session-undo` and
`edit-repaint-set`), and of the splice over a whole program's parts
(`src/Effect4/Laws/Program/Typing/PartsTable.lean`, the claim `module-table-splices`).

* **Finite evaluations.** Which path `feed` takes. No theorem says which path an edit takes:
  - at the sketch battery's program (`x = 5; cell = Ref.make(x); Ref.set(cell, 7);
    Ref.get(cell)`), an edit that keeps the type, one that changes it, and one at an address that
    holds no program;
  - at seat HOST's client with the Queue's definitions installed (a block at the root), every
    sub-program wrapped in `suspend`, which keeps its type: inside a body and inside the main
    program alike, each edit below the root splices;
  - at a sketch with one hole, the hole filled at its declared type;
  - omissions at the focus's exact type, at the sketch battery's program and at every typed
    address of the client's program.
* **Reader.** The undo law at the real session.
-/

namespace Test.Program.EditControls

open Effect4 Effect4.Program
open Test.Program.SketchControls
open Test.Program.PartsControls (sketchOf definedClient)

/-- The session opened on the sketch battery's program, a sketch with no hole. -/
def opened : EditSession := EditSession.open {} original

/-- The edit that keeps the type: `succeed 6` for `succeed 5`. -/
def keep : Edit := .fill [0] (.succeed (.lit (.nat 6)))

/-- The edit that changes the type: `succeed "x"` for `succeed 5`. -/
def change : Edit := .fill [0] (.succeed (.lit (.str "x")))

/-- The addresses a spliced delta shows again; `none` for any other delta. -/
def shownOf : Edit.Delta → Option (List (List Nat))
  | .spliced shown => some shown
  | _ => none

-- finite evaluation: the edit that keeps the type is spliced, and shows one address of the
-- table's seven, the edited leaf
#guard (shownOf (opened.feed keep).2, opened.table.length) = (some [[0]], 7)
-- finite evaluation: the edit that changes the type checks the table again, and the view shows
-- one refusal and no type, where the opened session shows none and a type
#guard ((opened.feed change).2, (opened.feed change).1.view.refusals.length,
  (opened.feed change).1.view.type.isSome, opened.view.refusals.length, opened.view.type.isSome) =
  (.rechecked, 1, false, 0, true)
-- finite evaluation: an address that holds no program changes nothing
#guard (opened.feed (.fill [7] (.succeed (.lit (.nat 6))))).2 = .unchanged

/-- At every address of a program of a sketch, the edit that wraps the sub-program in `suspend`:
the addresses where it splices, and those where it checks again. -/
def wrapReport (s : Sketch) (app : SigApp) : List (List Nat) × List (List Nat) :=
  let l := EditSession.open app s
  let results : List (List Nat × Edit.Delta) := (Node.addresses (.eff s.program)).filterMap fun a =>
    match (Node.eff s.program).at_ a with
    | some (.eff q) => some (a, (l.feed (.fill a (.suspend q))).2)
    | _ => none
  ((results.filter fun r => (shownOf r.2).isSome).map (·.1),
    (results.filter fun r => r.2 == .rechecked).map (·.1))

-- finite evaluation: at the client with the Queue's definitions, 103 of the 104 program
-- addresses splice, inside the bodies under `[0]` and inside the main program under `[1]`; only
-- the root checks again
#guard (sketchOf definedClient).map (fun (s, app) =>
  let r := wrapReport s app
  (r.1.length, r.1.any (·.head? == some 0), r.1.any (·.head? == some 1), r.2)) =
  some (103, true, true, [[]])

-- finite evaluation: at a sketch with one hole of type `number`, filling the hole with
-- `succeed 5` splices one entry, and the sketch keeps a type and no refusal
#guard (let l := EditSession.open {} (sketchAt .nat)
  let l' := l.feed (.fill [0] (.succeed (.lit (.nat 5))))
  (shownOf l'.2, l'.1.view.type.isSome, l'.1.view.refusals.length)) = (some [[0]], true, 0)

/-- The omission at an address with the hole row that declares the focus's type exactly. -/
def omitExact (l : EditSession) (a : List Nat) : Option Edit :=
  (l.sketch.focusAt l.app a).map fun f =>
    .omitAt a (Row.hole "h" f.ty.answer f.ty.error f.ty.requires.elems)

-- finite evaluation (the claim `omit-splices-table`): omitting the last statement at its type
-- splices one entry, the hole's, and the sketch keeps its type and has no refusal
#guard ((omitExact opened [1, 1, 1]).map fun e =>
  let l' := opened.feed e
  (shownOf l'.2, l'.1.view.type == opened.view.type, l'.1.view.refusals.length)) =
  some (some [[1, 1, 1]], true, 0)

-- finite evaluation: at the client with the Queue's definitions, every omission at a typed
-- address below the root with its exact row splices, inside the bodies and the main program
#guard (sketchOf definedClient).map (fun (s, app) =>
  let l := EditSession.open app s
  let results : List (List Nat × Edit.Delta) := (Node.addresses (.eff s.program)).filterMap fun a =>
    if a = [] then none else (omitExact l a).map fun e => (a, (l.feed e).2)
  (results.length, (results.filter fun r => (shownOf r.2).isSome).length)) = some (103, 103)

-- reader: the undo law at the opened session; both premises are evaluations of the lens
example : ((opened.feed keep).1.feed (.fill [0] (.succeed (.lit (.nat 5))))).1 = opened :=
  EditSession.feed_undo (s' := { program := context (.succeed (.lit (.nat 6))) })
    (EditSession.open_coherent _ _) rfl rfl

end Test.Program.EditControls
