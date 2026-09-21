import Effect4.Laws.Program.Typed.TypedStateDecl
import Effect4.Laws.Auto.Obligations
import Effect4.Machine.Stores

/-! Phase B statements and command controls for generated indexed columns.
All propositions are wanted obligations, with no authored proof bodies. Preserve this
pre-search copy before allowing the instrument to discharge already-closed projections. -/
open Effect4.Program.Typed Effect4.Machine

namespace Test.IndexedColumnDraft
inductive Expect | root
structure Cell where
  payload : Val
structure Sample where
  refs : List Val
  cells : List Cell

def sources : List Row := [
  ("Test.IndexedColumnDraft.Sample.refs", .column "HeapCell" (some "Effect4.Machine.RefKey.mk")),
  ("Test.IndexedColumnDraft.Sample.cells", .column "PromiseCell" (some "Effect4.Machine.DeferredKey.mk")),
  ("Test.IndexedColumnDraft.Cell.payload", .column "PromiseTable")]

#typed_state Test.IndexedColumnDraft.Sample using sources
-- The exact occurrence owns Cell.payload: no PromiseTable field may be emitted here.
def onlyLeafPredicates : Preds Unit := ⟨fun _ _ _ => True, fun _ _ _ => True⟩
def refLeafType {W : Type} (P : Preds W) : W → RefKey → Val → Prop := P.HeapCell
def cellLeafType {W : Type} (P : Preds W) : W → DeferredKey → Cell → Prop := P.PromiseCell

theorem refs_projection {W : Type} (P : Preds W) (w : W) (x : Sample) :
    ProofGraph.Obligation (SampleOk P w .root x →
      ∀ i v, x.refs[i]? = some v → P.HeapCell w ⟨i⟩ v) := ⟨⟩

theorem cells_projection {W : Type} (P : Preds W) (w : W) (x : Sample) :
    ProofGraph.Obligation (SampleOk P w .root x →
      ∀ i v, x.cells[i]? = some v → P.PromiseCell w ⟨i⟩ v) := ⟨⟩

theorem construct {W : Type} (P : Preds W) (w : W) (x : Sample) :
    ProofGraph.Obligation ((∀ i v, x.refs[i]? = some v → P.HeapCell w ⟨i⟩ v) →
      (∀ i v, x.cells[i]? = some v → P.PromiseCell w ⟨i⟩ v) → SampleOk P w .root x) := ⟨⟩

theorem empty {W : Type} (P : Preds W) (w : W) :
    ProofGraph.Obligation (SampleOk P w .root ⟨[], []⟩) := ⟨⟩

def onlyFirst : Preds Unit := ⟨fun _ key _ => key.index = 0, fun _ _ _ => True⟩
theorem duplicate_position (v : Val) :
    ProofGraph.Obligation (¬ SampleOk onlyFirst () .root ⟨[v, v], []⟩) := ⟨⟩
#proof_wanted duplicate_position
end Test.IndexedColumnDraft

namespace Test.IndexedColumnDraft.Sibling
inductive Expect | root
structure Cell where
  payload : Val
structure Sample where
  cells : List Cell
  due : List Cell

def sources : List Row := [
  ("Test.IndexedColumnDraft.Sibling.Sample.cells", .column "PromiseCell" (some "Effect4.Machine.DeferredKey.mk")),
  ("Test.IndexedColumnDraft.Sibling.Cell.payload", .column "PromiseTable")]
/-- error: typed state: column PromiseTable at Test.IndexedColumnDraft.Sibling.Cell.payload has no column owner -/
#guard_msgs in
#typed_state Test.IndexedColumnDraft.Sibling.Sample using sources

#typed_state Test.IndexedColumnDraft.Sibling.Sample using sources columns Test.IndexedColumnDraft.Sibling.Sample
-- Owning cells cannot make the sibling due occurrence disappear.
theorem due_required {W : Type} (P : Preds W) (w : W) (x : Sample) :
    ProofGraph.Obligation (SampleOk P w .root x → P.PromiseTable w x) := ⟨⟩
end Test.IndexedColumnDraft.Sibling

namespace Test.IndexedColumnDraft.NoIndex
inductive Expect | root
structure Sample where
  refs : List Val
def sources : List Row := [("Test.IndexedColumnDraft.NoIndex.Sample.refs", .column "HeapCell")]
/-- error: typed state: list column Test.IndexedColumnDraft.NoIndex.Sample.refs needs key-constructor metadata -/
#guard_msgs in
#typed_state Test.IndexedColumnDraft.NoIndex.Sample using sources columns Test.IndexedColumnDraft.NoIndex.Sample
end Test.IndexedColumnDraft.NoIndex

namespace Test.IndexedColumnDraft.NonList
inductive Expect | root
structure Sample where
  refs : Option Val
def sources : List Row := [("Test.IndexedColumnDraft.NonList.Sample.refs", .column "HeapCell" (some "Effect4.Machine.RefKey.mk"))]
/-- error: typed state: indexed column Test.IndexedColumnDraft.NonList.Sample.refs requires List, got Option Val -/
#guard_msgs (error) in
#typed_state Test.IndexedColumnDraft.NonList.Sample using sources
end Test.IndexedColumnDraft.NonList

namespace Test.IndexedColumnDraft.BadConstructor
inductive Expect | root
structure Sample where
  refs : List Val
def sources : List Row := [("Test.IndexedColumnDraft.BadConstructor.Sample.refs", .column "HeapCell" (some "Bool.true"))]
/-- error: typed state: Test.IndexedColumnDraft.BadConstructor.Sample.refs key constructor must have shape Nat → Key -/
#guard_msgs in
#typed_state Test.IndexedColumnDraft.BadConstructor.Sample using sources
end Test.IndexedColumnDraft.BadConstructor

namespace Test.IndexedColumnDraft.Collision
inductive Expect | root
structure Sample where
  refs : List Val
  other : List Val
def sources : List Row := [
  ("Test.IndexedColumnDraft.Collision.Sample.refs", .column "Same" (some "Effect4.Machine.RefKey.mk")),
  ("Test.IndexedColumnDraft.Collision.Sample.other", .column "Same" (some "Effect4.Machine.DeferredKey.mk"))]
/-- error: typed state: incompatible uses of predicate Same -/
#guard_msgs in
#typed_state Test.IndexedColumnDraft.Collision.Sample using sources
end Test.IndexedColumnDraft.Collision

namespace Test.IndexedColumnDraft.NatDirect
inductive Expect | root
structure Sample where
  items : List Nat

def sources : List Row := [
  ("Test.IndexedColumnDraft.NatDirect.Sample.items",
    .column "NatCell" (some "Effect4.Machine.RefKey.mk"))]

#typed_state Test.IndexedColumnDraft.NatDirect.Sample using sources

-- Nat is a census stop, but the explicit indexed field still supplies one leaf and column.
def onlyLeafPredicate : Preds Unit := ⟨fun _ _ _ => True⟩
def leafType {W : Type} (P : Preds W) : W → RefKey → Nat → Prop := P.NatCell
def columnType {W : Type} (leaf : W → RefKey → Nat → Prop) : W → List Nat → Prop :=
  Columns.Sample_items leaf

theorem projection {W : Type} (P : Preds W) (w : W) (x : Sample) :
    ProofGraph.Obligation (SampleOk P w .root x →
      ∀ i v, x.items[i]? = some v → P.NatCell w ⟨i⟩ v) := ⟨⟩
end Test.IndexedColumnDraft.NatDirect

namespace Test.IndexedColumnDraft.NatNested
inductive Expect | root
structure Leaf (α : Type) where
  items : List α
structure Sample where
  child : Leaf Nat

def sources : List Row := [
  ("Test.IndexedColumnDraft.NatNested.Leaf.items",
    .column "NatCell" (some "Effect4.Machine.RefKey.mk"))]

#typed_state Test.IndexedColumnDraft.NatNested.Sample using sources

-- The child must be entered from actual constructor metadata, after dropping its parameter.
def onlyLeafPredicate : Preds Unit := ⟨fun _ _ _ => True⟩
def leafType {W : Type} (P : Preds W) : W → RefKey → Nat → Prop := P.NatCell
def columnType {W : Type} (leaf : W → RefKey → Nat → Prop) : W → List Nat → Prop :=
  Columns.Leaf_items leaf

theorem projection {W : Type} (P : Preds W) (w : W) (x : Sample) :
    ProofGraph.Obligation (SampleOk P w .root x →
      ∀ i v, x.child.items[i]? = some v → P.NatCell w ⟨i⟩ v) := ⟨⟩
end Test.IndexedColumnDraft.NatNested

#typed_state_obligations Test.IndexedColumnDraft ceiling 8 using aesop (rule_sets := [Effect4.TypedState])
