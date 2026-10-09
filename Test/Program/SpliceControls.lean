import Effect4.Laws.Program.Typing.Splice
import Test.Program.SketchControls

/-!
Controls of the splice law (`table_splice`, `src/Effect4/Laws/Program/Typing/Splice.lean`, the
claim `edit-splices-table`) at the sketch battery's program: `x = 5; cell = Ref.make(x);
Ref.set(cell, 7); Ref.get(cell)`. Each line is a finite evaluation of the edited program's table
against the splice of the old table with the new subtree's.

* **Reader.** An edit of the first child that keeps its type (`succeed 6` for `succeed 5`): the
  splice is the edited program's table.
* **Red control.** An edit that changes the type (`succeed "x"`): the continuation's entries
  change (the cell holds a string, and `Ref.set(cell, 7)` is refused), so the splice is not the
  table. This is why the law keeps the focus's type as a premise.
-/

namespace Test.Program.SpliceControls

open Effect4 Effect4.Program
open Test.Program.SketchControls

/-- The empty application's typing signature. -/
def sig : Signature NativeOp := ({} : SigApp).signature

/-- An edit at an address: the edited program's table, and the splice of the old table with the
new subtree's table at the focus's environment. -/
def splicedAt (p : NativeEff) (a : List Nat) (q' : NativeEff) :
    Option (List Table.Entry × List Table.Entry) :=
  (focusAt sig [] p a).bind fun f =>
    match (Node.eff p).replaceAt a (.eff q') with
    | some (.eff p') => some (table sig [] p',
        Table.splice (table sig [] p) a (tableAt sig (some (.env f.env)) (.eff q') a))
    | _ => none

-- reader: an edit that keeps the type splices the table
#guard (splicedAt original [0] (.succeed (.lit (.nat 6)))).map (fun r => r.1 == r.2) = some true
-- red control: an edit that changes the type does not
#guard (splicedAt original [0] (.succeed (.lit (.str "x")))).map (fun r => r.1 == r.2) = some false

end Test.Program.SpliceControls
