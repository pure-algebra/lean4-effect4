import Test.Audit.IndexedColumns
import Test.Audit.IndexedColumnActual
import Effect4.Laws.Program.Typed.TypedStateDecl
import Effect4.Laws.Program.Typed.Contracts
import Effect4.Store.Carrier.Val
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

namespace Test.TypedStateDecl.WholeOwner
inductive Expect | root
structure Sample where
  value : Effect4.Store.Val
  token : Nat
def sources : List Row := [("Test.TypedStateDecl.WholeOwner.Sample", .owner "Whole")]
#typed_state Test.TypedStateDecl.WholeOwner.Sample using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Sample)
    (h : SampleOk P w e x) : P.Whole w e x := h.c0

def omitted : List Row := []
/-- error: typed state: missing source for Test.TypedStateDecl.WholeOwner.Sample.value -/
#guard_msgs in
#typed_state Test.TypedStateDecl.WholeOwner.Sample using omitted

def duplicate : List Row := sources ++
  [("Test.TypedStateDecl.WholeOwner.Sample.value", .custom "Value")]
/-- error: typed state: duplicate owner coverage at Test.TypedStateDecl.WholeOwner.Sample.value -/
#guard_msgs in
#typed_state Test.TypedStateDecl.WholeOwner.Sample using duplicate
-- Plain metadata fields are beneath an owner too, despite not being value positions.
def metadataDuplicate : List Row := sources ++
  [("Test.TypedStateDecl.WholeOwner.Sample.token", .custom "Token")]
/-- error: typed state: duplicate owner coverage at Test.TypedStateDecl.WholeOwner.Sample.token -/
#guard_msgs in
#typed_state Test.TypedStateDecl.WholeOwner.Sample using metadataDuplicate
end Test.TypedStateDecl.WholeOwner

namespace Test.TypedStateDecl.ConstructorOwner
inductive Expect | root
inductive Task where
  | done
  | resume (target : Nat) (token : Nat) (answer : Effect4.Store.Val)
def sources : List Row := [("Test.TypedStateDecl.ConstructorOwner.Task.resume", .owner "Resume")]
#typed_state Test.TypedStateDecl.ConstructorOwner.Task using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (target token : Nat)
    (answer : Effect4.Store.Val) : TaskOk P w e (.resume target token answer) ↔
      P.Resume w e target token answer := Iff.rfl
end Test.TypedStateDecl.ConstructorOwner

namespace Test.TypedStateDecl.SingleConstructorOwner
inductive Expect | root
inductive Box where
  | pack (token : Nat) (value : Effect4.Store.Val)
def sources : List Row := [("Test.TypedStateDecl.SingleConstructorOwner.Box.pack", .owner "Packed")]
#typed_state Test.TypedStateDecl.SingleConstructorOwner.Box using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (token : Nat) (value : Effect4.Store.Val) :
    BoxOk P w e (.pack token value) ↔ P.Packed w e token value := Iff.rfl
end Test.TypedStateDecl.SingleConstructorOwner

namespace Test.TypedStateDecl.SharedOwner
inductive Expect | root
structure Child where
  value : Effect4.Store.Val
structure Wrapped where
  child : Child
structure Parent where
  owned : Wrapped
  shared : Child
def sources : List Row := [
  ("Test.TypedStateDecl.SharedOwner.Wrapped", .owner "Whole"),
  ("Test.TypedStateDecl.SharedOwner.Child.value", .value .inherited)]
#typed_state Test.TypedStateDecl.SharedOwner.Parent using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Parent)
    (h : ParentOk P w e x) : P.Whole w e x.owned ∧ P.value w e x.shared.value :=
  ⟨h.c0.c0, h.c1.c0⟩
-- The shared child needs its row on the path outside the whole owner.
def missing : List Row := [("Test.TypedStateDecl.SharedOwner.Wrapped", .owner "Whole")]
/-- error: typed state: missing source for Test.TypedStateDecl.SharedOwner.Child.value -/
#guard_msgs in
#typed_state Test.TypedStateDecl.SharedOwner.Parent using missing
-- With only the wrapped path, the descendant row becomes duplicate coverage.
/-- error: typed state: duplicate owner coverage at Test.TypedStateDecl.SharedOwner.Child.value -/
#guard_msgs in
#typed_state Test.TypedStateDecl.SharedOwner.Wrapped using sources
end Test.TypedStateDecl.SharedOwner

namespace Test.TypedStateDecl.ActualOwners
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

def readsMetadata : Effect4.Program.Typed.Preds Unit where
  SavedOk := fun _ _ x => x.interruptible = true
  PendingOk := fun _ _ _ => True
  ServiceOk := fun _ _ _ => True
  exit := fun _ _ _ => True
  ResumeOk := fun _ _ target token _ => target = ⟨4⟩ ∧ token = 7
  HeapCell := fun _ _ _ => True
  PromiseCell := fun _ _ _ => True
  PromiseTable := fun _ _ => True
  CaptureOk := fun _ _ c => c.path = [2] ∧ c.root = 7 ∧ c.env = [] ∧ c.ctx = emptyCtx
  RaceOk := fun _ _ _ => True

def answer : RProgram := .pure (.success .unit)

theorem resume_accepted : TaskOk readsMetadata () .root (.resume ⟨4⟩ 7 answer) := ⟨rfl, rfl⟩
theorem resume_token_distinguished : ¬ TaskOk readsMetadata () .root (.resume ⟨4⟩ 8 answer) := by
  intro h
  have bad : (8 : Nat) = 7 := h.2
  cases bad
theorem resume_target_distinguished : ¬ TaskOk readsMetadata () .root (.resume ⟨5⟩ 7 answer) := by
  intro h
  cases h.1
theorem command_token_distinguished : ¬ CmdOk readsMetadata () .root (.resume ⟨4⟩ 8 answer) := by
  intro h
  have bad : (8 : Nat) = 7 := h.2
  cases bad

def capture : Capture := ⟨[2], [], 0, [], emptyCtx, 7⟩
theorem capture_accepted : CaptureOk readsMetadata () .root capture := ⟨rfl, rfl, rfl, rfl⟩
theorem capture_path_distinguished :
    ¬ CaptureOk readsMetadata () .root { capture with path := [3] } := by
  intro h
  cases h.c0.1
theorem capture_root_distinguished :
    ¬ CaptureOk readsMetadata () .root { capture with root := 8 } := by
  intro h
  have bad : (8 : Nat) = 7 := h.c0.2.1
  cases bad

def saved : RSaved := ⟨answer, [], true, none, false⟩
theorem saved_accepted : RSavedOk readsMetadata () .root saved := ⟨rfl⟩
theorem saved_flag_distinguished :
    ¬ RSavedOk readsMetadata () .root { saved with interruptible := false } := by
  intro h
  have bad : false = true := h.c0
  cases bad

#print axioms resume_token_distinguished
#print axioms resume_target_distinguished
#print axioms capture_path_distinguished
#print axioms capture_root_distinguished
#print axioms saved_flag_distinguished
end Test.TypedStateDecl.ActualOwners

namespace Test.TypedStateDecl.TokenContracts
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed

def declared : Effect4.Program.Typed.World :=
  (worldGood.addToken ⟨4⟩ 7 (EffTy.pure .nat)).addToken ⟨5⟩ 7 (EffTy.pure .bool)

-- Token numbers are local to a fiber. A second fiber's same-numbered token retains both.
theorem local_tokens : declared.Θ ⟨4⟩ 7 = some (EffTy.pure .nat) ∧
    declared.Θ ⟨5⟩ 7 = some (EffTy.pure .bool) := ⟨rfl, rfl⟩

def acceptsNat (_w : Effect4.Program.Typed.World) (ty : EffTy) (_code : RProgram) : Prop := ty.answer = .nat

theorem typed_resume : Contracts.ResumeOk acceptsNat declared ⟨4⟩ 7 ActualOwners.answer := by
  intro ty found
  change some (EffTy.pure .nat) = some ty at found
  cases found
  rfl

theorem wrong_target_type :
    ¬ Contracts.ResumeOk acceptsNat declared ⟨5⟩ 7 ActualOwners.answer := by
  intro h
  have bad := h (EffTy.pure .bool) rfl
  cases bad

-- Replacing a declared token's type is not growth in the world order.
theorem token_replacement_refused :
    ¬ declared.le (declared.addToken ⟨4⟩ 7 (EffTy.pure .bool)) := by
  intro h
  have bad := h.2.2.2.2.2 ⟨4⟩ 7 (EffTy.pure .nat) rfl
  change some (EffTy.pure .bool) = some (EffTy.pure .nat) at bad
  cases bad

#print axioms typed_resume
#print axioms token_replacement_refused
end Test.TypedStateDecl.TokenContracts
