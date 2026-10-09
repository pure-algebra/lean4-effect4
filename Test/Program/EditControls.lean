import Effect4.Laws.Program.Edit
import Test.Program.SpliceControls

/-!
Readers and controls of the edit session (`src/Effect4/Program/Edit.lean`, its laws
`src/Effect4/Laws/Program/Edit.lean`, the claims `edit-session-coherent`, `edit-session-undo` and
`edit-repaint-set`), at the sketch battery's program: `x = 5; cell = Ref.make(x);
Ref.set(cell, 7); Ref.get(cell)`.

* **Finite evaluations.** Which path `feed` takes on three edits: one that keeps the type
  (spliced, showing only the new subtree), one that changes it (rechecked, and the view shows the
  refusal at the set), one at an address that holds no program (unchanged). No theorem says which
  path an edit takes.
* **Reader.** The undo law at the real session: the spliced edit, then the old sub-program put
  back, gives the opened session again.
-/

namespace Test.Program.EditControls

open Effect4 Effect4.Program
open Test.Program.SketchControls Test.Program.SpliceControls

/-- The session opened on the program. -/
def opened : EditSession NativeOp := EditSession.open sig [] original

/-- The edit that keeps the type: `succeed 6` for `succeed 5`. -/
def keep : Edit NativeOp := .replace [0] (.succeed (.lit (.nat 6)))

/-- The edit that changes the type: `succeed "x"` for `succeed 5`. -/
def change : Edit NativeOp := .replace [0] (.succeed (.lit (.str "x")))

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
#guard (opened.feed (.replace [7] (.succeed (.lit (.nat 6))))).2 = .unchanged

-- reader: the undo law at the opened session; both premises are evaluations of the lens
example : ((opened.feed keep).1.feed (.replace [0] (.succeed (.lit (.nat 5))))).1 = opened :=
  EditSession.feed_undo (p' := context (.succeed (.lit (.nat 6)))) (EditSession.open_coherent _ _ _)
    rfl rfl

end Test.Program.EditControls
