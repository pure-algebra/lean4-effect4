import Test.Dogfood.Proofs.QueueWorkersWriteCensus
import Effect4.Laws.Program.CodeClosure.Qualified.Stable

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, through ordinary source segments around classified queue operations.
The existing qualified family carries callbacks outside queue and assignment writers.
Actual initialized authority separately excludes setters and new reference allocations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersReadonly
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- These source segments exclude queue commits and assignment appends. -/
def head : Node NativeOp → Bool
  | .eff (.perform (.refModifyWith _) _) => false
  | .eff (.perform (.refUpdateWith _) request) => decide (request ≠ .var 0 ∧ request ≠ .var 3)
  | _ => true

/-- Every actual descendant of the selected source point satisfies the local exclusion. -/
def Below (root : NativeEff) (origin : List Nat) : Prop :=
  ∀ path node, origin.IsPrefix path → Node.at_ (.eff root) path = some node → head node = true

/-- Descending to an existing child retains every source exclusion. -/
theorem Below.append {root : NativeEff} {origin : List Nat} (held : Below root origin) (suffix : List Nat) :
    Below root (origin ++ suffix) := by
  intro path node inside found
  exact held path node ((List.prefix_append_of_prefix (List.prefix_refl origin)).trans inside) found

/-- Ordinary source points retain their fixed root references and their excluded writer region. -/
def PointAt (total : Nat) (point : Point) : Prop :=
  Below (Programs.queueProgram total) point.path ∧ AnswerSlots.Prefix InitialSlots.bindings point.env

/-- Update operations in this source family cannot change either observed job destination. -/
def Writes : SyncOp → Prop
  | .refUpdate key _ _ | .refUpdateAndGet key _ _ => key.index ≠ 0 ∧ key.index ≠ 3
  | _ => False

/-- Actual callbacks append only their returned argument to the immutable leading bindings. -/
theorem transport (total : Nat) :
    CodeClosure.Qualified.Transport (PointAt total) (AnswerSlots.Prefix InitialSlots.bindings) where
  environment := fun held => held.2
  child := fun held _ => ⟨held.1.append _, held.2⟩
  childWith := fun held _ value => ⟨held.1.append _, held.2.append [value]⟩
  capture := fun held value _ => ⟨held.1, held.2.append [value]⟩

/-- A declared root reference read selects its fixed allocated index. -/
theorem read_index (point : Point) (index key : Nat) (small : index < 5)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (read : evalTerm point.env (.var index) = some (.cell ⟨key⟩)) : key = index := by
  change point.env[index]? = some (.cell ⟨key⟩) at read
  have slot := leading.read index (by change index < 6; omega)
  have binding : InitialSlots.bindings[index]? = some (.cell ⟨index⟩) := by
    rcases index with _ | _ | _ | _ | _ | index
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (show False by omega).elim
  have same := Option.some.inj (binding.symm.trans (slot.symm.trans read))
  cases same
  rfl

/-- The actual writer census and fixed slots establish each local operation exclusion. -/
theorem operation (total : Nat) (point : Point) (row : NativeOp) (request : Term) (value : Val)
    (op : SyncOp) (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.perform row request)))
    (held : PointAt total point) (reads : evalTerm point.env request = some value)
    (converted : row.syncOpOf point.env value = some op) :
    CodeClosure.Qualified.OpAt (PointAt total) (AnswerSlots.Prefix InitialSlots.bindings) Writes op := by
  have safe := held.1 point.path _ (List.prefix_refl _) found
  have checked := QueueWorkersWriteCensus.source_head total point.path _ found
  generalize envEq : point.env = env at converted
  revert converted
  fun_cases NativeOp.syncOpOf row env value
  all_goals intro converted
  case case21 => cases converted
  all_goals cases converted
  case case6 term index =>
    have destination : WriterSource.Destination point.path request := of_decide_eq_true checked
    have excluded : request ≠ .var 0 ∧ request ≠ .var 3 := of_decide_eq_true safe
    rcases destination with zero | one | three | four | ⟨two, _path⟩
    · exact (excluded.1 zero).elim
    · subst request
      cases read_index point 1 index (by decide) held.2 reads
      exact ⟨by decide, by decide⟩
    · exact (excluded.2 three).elim
    · subst request
      cases read_index point 4 index (by decide) held.2 reads
      exact ⟨by decide, by decide⟩
    · subst request
      cases read_index point 2 index (by decide) held.2 reads
      exact ⟨by decide, by decide⟩
  case case8 term index =>
    have destination : request = .var 4 := of_decide_eq_true checked
    subst request
    cases read_index point 4 index (by decide) held.2 reads
    exact ⟨by decide, by decide⟩
  case case12 => cases safe
  case case7 | case9 | case10 | case11 | case13 => cases checked
  all_goals trivial

/-- Source compilation and actual callbacks reuse the one qualified producer. -/
theorem contract (total : Nat) :
    CodeClosure.Qualified.Contract (Programs.queueProgram total) (PointAt total)
      (AnswerSlots.Prefix InitialSlots.bindings) Writes where
  compilation := CodeClosure.Qualified.compile_contract _ _ _ _ (transport total)
    (fun point row request value op found held reads converted => operation total point row request value op found held reads converted)
  child := (transport total).child
  childWith := (transport total).childWith
  capture := (transport total).capture

/-- Actual ordinary code uses the existing source graph and saved-family implementation. -/
abbrev Code (total : Nat) := CodeClosure.Qualified.CodeAt (PointAt total)
  (AnswerSlots.Prefix InitialSlots.bindings) Writes

/-- The unit answer family supplies ordinary current heads and saved callbacks. -/
def laws (total : Nat) (fragment : SourceScope.Fragment (Programs.queueProgram total)) (table : RowTable) :=
  CodeClosure.Qualified.prefixLaws (Programs.queueProgram total) fragment _ _ _
    (contract total) (fun _ held _ => held) table
end Test.Dogfood.Proofs.QueueWorkersReadonly
