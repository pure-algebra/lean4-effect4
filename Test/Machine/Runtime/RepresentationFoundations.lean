import Effect4.Laws.Machine.Refinement

/-! C2/C3/C4 controls: heterogeneous cells, invariant domains, answers and frontiers.
The small projection chain is a mathematical fixture, not a host implementation. -/
set_option autoImplicit false
namespace Test.Machine.RepresentationFoundations
open Effect4 Effect4.Machine Effect4.Machine.Refinement

def indexed : Nat → Val → Prop
  | 0, value => ∃ n : Nat, value = .nat n
  | _ + 1, value => ∃ bit : Bool, value = .bool bit

def mixed : RefHeap := [.nat 7, .bool true]
def boolWrite : RefKernel := fun _ => some (.cell ⟨1⟩, some (.bool false))

theorem mixed_typed : ∀ index value, refPeek mixed ⟨index⟩ = some value → indexed index value := by
  intro index value lookup
  cases index with
  | zero =>
    change some (Val.nat 7) = some value at lookup
    cases lookup
    exact ⟨7, rfl⟩
  | succ index =>
    cases index with
    | zero =>
      change some (Val.bool true) = some value at lookup
      cases lookup
      exact ⟨true, rfl⟩
    | succ index => cases lookup

theorem boolWrite_keeps : RefKernel.Keeps (indexed 1) (fun answer => answer = .cell ⟨1⟩) boolWrite := by
  intro current result _ ran
  change some (Val.cell ⟨1⟩, some (Val.bool false)) = some result at ran
  cases ran
  refine ⟨rfl, ?_⟩
  intro next written
  cases written
  exact ⟨false, rfl⟩

theorem heterogeneous_update :
    (Val.cell ⟨1⟩ = Val.cell ⟨1⟩) ∧
    (∀ index value, refPeek [.nat 7, .bool false] ⟨index⟩ = some value → indexed index value) ∧
    ([Val.nat 7, .bool false].length = mixed.length) ∧
    (∀ index, index ≠ 1 → refPeek [.nat 7, .bool false] ⟨index⟩ = refPeek mixed ⟨index⟩) :=
  indexed_ref_step_preserves indexed (fun answer => answer = .cell ⟨1⟩)
    (.refSet ⟨1⟩ (.bool false)) ⟨1⟩ boolWrite mixed [.nat 7, .bool false] (.cell ⟨1⟩)
    rfl mixed_typed boolWrite_keeps rfl

theorem no_write_keeps : RefKernel.Keeps (indexed 0) (indexed 0) (fun value => some (value, none)) := by
  intro value result typed ran
  cases ran
  exact ⟨typed, fun _ impossible => by cases impossible⟩

theorem heterogeneous_read :
    indexed 0 (.nat 7) ∧
    (∀ index value, refPeek mixed ⟨index⟩ = some value → indexed index value) ∧
    mixed.length = mixed.length ∧
    (∀ index, index ≠ 0 → refPeek mixed ⟨index⟩ = refPeek mixed ⟨index⟩) :=
  indexed_ref_step_preserves indexed (indexed 0) (.refGet ⟨0⟩) ⟨0⟩
    (fun value => some (value, none)) mixed mixed (.nat 7)
    rfl mixed_typed no_write_keeps rfl

/-- The machine can execute an ill-typed write; C2 must retain its kernel premise. -/
theorem wrong_write_runs : refStep (.refSet ⟨1⟩ (.nat 9)) mixed =
    some (.cell ⟨1⟩, [.nat 7, .nat 9]) := rfl

theorem wrong_write_refused : ¬ RefKernel.Keeps (indexed 1) (fun _ => True)
    (fun _ => some (.cell ⟨1⟩, some (.nat 9))) := by
  intro keeps
  have written := (keeps (.bool true) (.cell ⟨1⟩, some (.nat 9)) ⟨true, rfl⟩ rfl).2 (.nat 9) rfl
  obtain ⟨bit, impossible⟩ := written
  cases impossible

theorem missing_cell_frontier : refStep (.refGet ⟨8⟩) mixed = none := rfl
theorem allocation_is_separate : (SyncOp.refMake (.nat 1)).refKernel = none := rfl
theorem absent_other_unchanged : refPeek (refWriteBack mixed ⟨1⟩ (some (.bool false))) ⟨8⟩ = none :=
  refWriteBack_peek_other mixed ⟨1⟩ (some (.bool false)) 8 (by decide)

/-- The named store bank supplies the generic indexed theorem. -/
theorem indexed_bank (P : Nat → Val → Prop) (Q : Val → Prop)
    (op : SyncOp) (cell : RefKey) (kernel : RefKernel) (before after : RefHeap) (answer : Val)
    (row : op.refKernel = some (cell, kernel))
    (typed : ∀ index value, refPeek before ⟨index⟩ = some value → P index value)
    (keeps : RefKernel.Keeps (P cell.index) Q kernel)
    (step : refStep op before = some (answer, after)) :
    Q answer ∧ (∀ index value, refPeek after ⟨index⟩ = some value → P index value) ∧
    after.length = before.length ∧
    (∀ index, index ≠ cell.index → refPeek after ⟨index⟩ = refPeek before ⟨index⟩) := by
  aesop (rule_sets := [Effect4.Stores])

-- The identical statement without the bank must fail.
/--
error: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
case left
P : Nat → Val → Prop
Q : Val → Prop
op : SyncOp
cell : RefKey
kernel : RefKernel
before after : RefHeap
answer : Val
row : op.refKernel = some (cell, kernel)
typed : ∀ (index : Nat) (value : Val), refPeek before { index := index } = some value → P index value
keeps : RefKernel.Keeps (P cell.index) Q kernel
step : refStep op before = some (answer, after)
⊢ Q answer

case right.left
P : Nat → Val → Prop
Q : Val → Prop
op : SyncOp
cell : RefKey
kernel : RefKernel
before after : RefHeap
answer : Val
row : op.refKernel = some (cell, kernel)
typed : ∀ (index : Nat) (value : Val), refPeek before { index := index } = some value → P index value
keeps : RefKernel.Keeps (P cell.index) Q kernel
step : refStep op before = some (answer, after)
index : Nat
value : Val
a : refPeek after { index := index } = some value
⊢ P index value

case right.right.left
P : Nat → Val → Prop
Q : Val → Prop
op : SyncOp
cell : RefKey
kernel : RefKernel
before after : RefHeap
answer : Val
row : op.refKernel = some (cell, kernel)
typed : ∀ (index : Nat) (value : Val), refPeek before { index := index } = some value → P index value
keeps : RefKernel.Keeps (P cell.index) Q kernel
step : refStep op before = some (answer, after)
⊢ List.length after = List.length before

case right.right.right
P : Nat → Val → Prop
Q : Val → Prop
op : SyncOp
cell : RefKey
kernel : RefKernel
before after : RefHeap
answer : Val
row : op.refKernel = some (cell, kernel)
typed : ∀ (index : Nat) (value : Val), refPeek before { index := index } = some value → P index value
keeps : RefKernel.Keeps (P cell.index) Q kernel
step : refStep op before = some (answer, after)
index : Nat
a : ¬index = cell.index
⊢ refPeek after { index := index } = refPeek before { index := index }
-/
#guard_msgs (error) in
example (P : Nat → Val → Prop) (Q : Val → Prop)
    (op : SyncOp) (cell : RefKey) (kernel : RefKernel) (before after : RefHeap) (answer : Val)
    (row : op.refKernel = some (cell, kernel))
    (typed : ∀ index value, refPeek before ⟨index⟩ = some value → P index value)
    (keeps : RefKernel.Keeps (P cell.index) Q kernel)
    (step : refStep op before = some (answer, after)) :
    Q answer ∧ (∀ index value, refPeek after ⟨index⟩ = some value → P index value) ∧
    after.length = before.length ∧
    (∀ index, index ≠ cell.index → refPeek after ⟨index⟩ = refPeek before ⟨index⟩) := by
  aesop

def first (state : Nat × Bool) : Nat × Bool := (state.1 + 1, state.2)
def second : Nat × Bool → Nat := Prod.fst
def concreteStep (op : Bool) (state : Nat × Bool) : Option ((Nat × Bool) × Nat) :=
  if op && state.2 then some ((state.1 + 1, state.2), state.1 + 1) else none
def middleStep (op : Bool) (state : Nat × Bool) : Option ((Nat × Bool) × Nat) :=
  if op && state.2 then some ((state.1 + 1, state.2), state.1) else none
def modelStep (op : Bool) (state : Nat) : Option (Nat × Nat) :=
  if op then some (state + 1, state) else none
def concreteValid (_ : Nat × Bool) : Prop := True
def middleValid (state : Nat × Bool) : Prop := state.2 = true

theorem first_projects : Projects first concreteStep middleStep concreteValid := by
  constructor
  · intro op state _
    obtain ⟨n, bit⟩ := state
    cases op <;> cases bit <;> rfl
  · intro _ _ _ _ _ _
    exact True.intro

theorem second_projects : Projects second middleStep modelStep middleValid := by
  constructor
  · intro op state valid
    obtain ⟨n, bit⟩ := state
    change bit = true at valid
    cases valid
    cases op <;> rfl
  · intro op state next answer valid step
    obtain ⟨n, bit⟩ := state
    change bit = true at valid
    cases valid
    cases op with
    | false => cases step
    | true => cases step; rfl

theorem composed : Projects (second ∘ first) concreteStep modelStep
    (fun state => concreteValid state ∧ middleValid (first state)) :=
  projects_compose first second concreteStep middleStep modelStep concreteValid middleValid
    first_projects second_projects

theorem induced : Refines
    (fun state model => (concreteValid state ∧ middleValid (first state)) ∧
      (second ∘ first) state = model) concreteStep modelStep :=
  projects_induces_refines _ _ _ _ composed

theorem missing_middle_invariant_refused :
    ¬ Projects (second ∘ first) concreteStep modelStep concreteValid := by
  intro projection
  have impossible := projection.step true (0, false) True.intro
  cases impossible

theorem missing_relation_invariant_refused :
    ¬ Refines (fun state model => (second ∘ first) state = model) concreteStep modelStep := by
  intro refinement
  have impossible := refinement.frontier true (0, false) 1 rfl rfl
  cases impossible

def wrongAnswerStep (op : Bool) (state : Nat) : Option (Nat × Nat) :=
  if op then some (state + 1, state + 1) else none

theorem changed_answer_refused : ¬ Projects (second ∘ first) concreteStep wrongAnswerStep
    (fun state => concreteValid state ∧ middleValid (first state)) := by
  intro projection
  have impossible := projection.step true (0, true) ⟨True.intro, rfl⟩
  cases impossible

theorem composed_success : ∃ model answer, modelStep true 1 = some (model, answer) ∧
    1 = answer ∧ (concreteValid (1, true) ∧ middleValid (first (1, true))) ∧
    (second ∘ first) (1, true) = model :=
  induced.step true (0, true) 1 (1, true) 1 ⟨⟨True.intro, rfl⟩, rfl⟩ rfl

theorem composed_frontier : modelStep false 1 = none :=
  induced.frontier false (0, true) 1 ⟨⟨True.intro, rfl⟩, rfl⟩ rfl

#print axioms heterogeneous_update
#print axioms heterogeneous_read
#print axioms wrong_write_refused
#print axioms indexed_bank
#print axioms composed
#print axioms induced
#print axioms missing_middle_invariant_refused
#print axioms missing_relation_invariant_refused
#print axioms changed_answer_refused
end Test.Machine.RepresentationFoundations
