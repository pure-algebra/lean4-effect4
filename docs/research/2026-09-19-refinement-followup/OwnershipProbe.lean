import Effect4.Laws.Auto.TypedStateDecl
import Effect4.Store.Val
set_option autoImplicit false
open Effect4.Program.Typed

namespace FollowupSkippedOccurrence
inductive Expect | root
structure CellStore where
  payload : Effect4.Store.Val
structure Parent where
  owned : CellStore
  unowned : CellStore
def sources : List Row := [
  ("FollowupSkippedOccurrence.CellStore.payload", .column "Heap"),
  ("FollowupSkippedOccurrence.Parent.owned", .custom "Owned")]
#typed_state FollowupSkippedOccurrence.Parent using sources
/-- With no column owner, a custom sibling exempts the other occurrence of CellStore. -/
theorem ignores_unowned {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (h : P.Owned w e x.owned) : ParentOk P w e x := ⟨h⟩
#print ParentOk
#print Preds
#print axioms ignores_unowned
end FollowupSkippedOccurrence

namespace FollowupColumnOwnership
inductive Expect | root
structure A where
  payload : Effect4.Store.Val
structure B where
  payload : Effect4.Store.Val
structure Parent where
  a : A
  b : B
def sources : List Row := [
  ("FollowupColumnOwnership.A.payload", .column "Heap"),
  ("FollowupColumnOwnership.B.payload", .column "Heap")]
#typed_state FollowupColumnOwnership.Parent using sources columns FollowupColumnOwnership.A
/-- A column on A does not inspect the unrelated B instance. -/
theorem ignores_b {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (h : P.Heap w x.a) : ParentOk P w e x := ⟨⟨h⟩⟩
#print ParentOk
#print Preds
#print axioms ignores_b
end FollowupColumnOwnership
