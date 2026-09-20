import Effect4.Laws.Auto.TypedStateDecl
import Effect4.Store.Val
open Effect4.Program.Typed

namespace Test.TypedStateDecl.Positive
inductive Expect | root
structure Sample where
  value : Effect4.Store.Val
def sources : List Row := [("Test.TypedStateDecl.Positive.Sample.value", .custom "ValueOk")]
#typed_state Test.TypedStateDecl.Positive.Sample using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Sample)
    (h : P.ValueOk w e x.value) : SampleOk P w e x := ⟨h⟩
end Test.TypedStateDecl.Positive

namespace Test.TypedStateDecl.Collision
inductive Expect | root
structure Sample where
  one : Option Effect4.Store.Val
  many : List Effect4.Store.Val
def sources : List Row := [
  ("Test.TypedStateDecl.Collision.Sample.one", .custom "Same"),
  ("Test.TypedStateDecl.Collision.Sample.many", .custom "Same")]
/-- error: typed state: incompatible uses of predicate Same -/
#guard_msgs in
#typed_state Test.TypedStateDecl.Collision.Sample using sources
end Test.TypedStateDecl.Collision

namespace Test.TypedStateDecl.Missing
inductive Expect | root
structure Sample where
  value : Effect4.Store.Val
def sources : List Row := []
/-- error: typed state: missing source for Test.TypedStateDecl.Missing.Sample.value -/
#guard_msgs in
#typed_state Test.TypedStateDecl.Missing.Sample using sources
end Test.TypedStateDecl.Missing

/-! The three omission shapes of the landed-architecture review (2026-09-19), as controls: a
field that is both a position and an edge, a single-constructor inductive that is not a
structure, and a nested column owner. Each clause is proved present by projection. -/

namespace Test.TypedStateDecl.Mixed
inductive Expect | root
structure Child where
  payload : Effect4.Store.Val
structure Parent where
  pair : Effect4.Store.Val × Child
def sources : List Row := [
  ("Test.TypedStateDecl.Mixed.Child.payload", .value .inherited),
  ("Test.TypedStateDecl.Mixed.Parent.pair", .value .inherited)]
#typed_state Test.TypedStateDecl.Mixed.Parent using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (h : ParentOk P w e x) : P.value w e x.pair.1 ∧ ChildOk P w e x.pair.2 := ⟨h.c0, h.c1⟩
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (h : ChildOk P w e x.pair.2) : P.value w e x.pair.2.payload := h.c0
end Test.TypedStateDecl.Mixed

namespace Test.TypedStateDecl.Single
inductive Expect | root
inductive Box where
  | mk (payload : Effect4.Store.Val)
def sources : List Row := [("Test.TypedStateDecl.Single.Box.payload", .value .inherited)]
#typed_state Test.TypedStateDecl.Single.Box using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (v : Effect4.Store.Val)
    (h : BoxOk P w e (.mk v)) : P.value w e v := h
end Test.TypedStateDecl.Single

namespace Test.TypedStateDecl.ColumnOnly
inductive Expect | root
structure Store where
  payload : Effect4.Store.Val
structure Parent where
  store : Store
def sources : List Row := [("Test.TypedStateDecl.ColumnOnly.Store.payload", .column "Heap")]
#typed_state Test.TypedStateDecl.ColumnOnly.Parent using sources columns Test.TypedStateDecl.ColumnOnly.Store
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (h : ParentOk P w e x) : P.Heap w x.store := h.c0.c0
end Test.TypedStateDecl.ColumnOnly

namespace Test.TypedStateDecl.SkippedOccurrence
inductive Expect | root
structure CellStore where
  payload : Effect4.Store.Val
structure Parent where
  owned : CellStore
  unowned : CellStore
def sources : List Row := [
  ("Test.TypedStateDecl.SkippedOccurrence.CellStore.payload", .column "Heap"),
  ("Test.TypedStateDecl.SkippedOccurrence.Parent.owned", .custom "Owned")]
-- A custom source on `owned` covers that field's subtree only; the sibling occurrence of the
-- same type under `unowned` is still checked (refinement follow-up §1, first probe).
/-- error: typed state: column Heap at Test.TypedStateDecl.SkippedOccurrence.CellStore.payload has no column owner -/
#guard_msgs in
#typed_state Test.TypedStateDecl.SkippedOccurrence.Parent using sources
end Test.TypedStateDecl.SkippedOccurrence

namespace Test.TypedStateDecl.ColumnOwnership
inductive Expect | root
structure A where
  payload : Effect4.Store.Val
structure B where
  payload : Effect4.Store.Val
structure Parent where
  a : A
  b : B
def sources : List Row := [
  ("Test.TypedStateDecl.ColumnOwnership.A.payload", .column "Heap"),
  ("Test.TypedStateDecl.ColumnOwnership.B.payload", .column "Heap")]
-- A column predicate named `Heap` emitted for `A` covers `A`'s occurrence, not `B`'s
-- (refinement follow-up §1, second probe).
/-- error: typed state: column Heap at Test.TypedStateDecl.ColumnOwnership.B.payload has no column owner -/
#guard_msgs in
#typed_state Test.TypedStateDecl.ColumnOwnership.Parent using sources columns Test.TypedStateDecl.ColumnOwnership.A
end Test.TypedStateDecl.ColumnOwnership

namespace Test.TypedStateDecl.NoColumnOwner
inductive Expect | root
structure Store where
  payload : Effect4.Store.Val
structure Parent where
  store : Store
def sources : List Row := [("Test.TypedStateDecl.NoColumnOwner.Store.payload", .column "Heap")]
/-- error: typed state: column Heap at Test.TypedStateDecl.NoColumnOwner.Store.payload has no column owner -/
#guard_msgs in
#typed_state Test.TypedStateDecl.NoColumnOwner.Parent using sources
end Test.TypedStateDecl.NoColumnOwner

