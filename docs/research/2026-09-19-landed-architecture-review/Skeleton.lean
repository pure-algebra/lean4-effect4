import Effect4.Laws.Auto.TypedStateDecl
import Effect4.Store.Val
open Effect4.Program.Typed

namespace Review.Mixed
inductive Expect | root
structure Child where
  payload : Effect4.Store.Val
structure Parent where
  pair : Effect4.Store.Val × Child
def sources : List Row := [
  ("Review.Mixed.Child.payload", .value .inherited),
  ("Review.Mixed.Parent.pair", .value .inherited)]
#position_census Review.Mixed.Parent
#typed_state Review.Mixed.Parent using sources
-- If accepted, the nested child's payload contributes no clause.
theorem firstOnly {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (onlyFirst : P.value w e x.pair.1) : ParentOk P w e x := ⟨onlyFirst⟩
#print ParentOk
#print axioms firstOnly
end Review.Mixed

namespace Review.Single
inductive Expect | root
inductive Box where
  | mk (payload : Effect4.Store.Val)
def sources : List Row := [("Review.Single.Box.payload", .value .inherited)]
#position_census Review.Single.Box
#typed_state Review.Single.Box using sources
-- If accepted, this admits every box regardless of the payload.
theorem everyBox {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Box) : BoxOk P w e x := by
  cases x
  exact True.intro
#print BoxOk
#print axioms everyBox
end Review.Single
