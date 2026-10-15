import Test.Dogfood.Proofs.QueueWorkersCountCell
import Effect4.Laws.Program.AnswerSlots.InitializedSync

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the independent actual counter-history invariant.
The initialized source certificate supplies the actual current writer and allocation index.
No job conservation premise classifies the counter's delayed reply.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersCountCell
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers

/-- Allocation keeps the optional Nat counter when its selected initial value is a Nat. -/
theorem make_keeps (initial : Val) (before after : Stores) (answer : Val)
    (actual : syncOpStep (.refMake initial) before = some (after, answer))
    (atCounter : before.refs.length = 4 → ∃ count, initial = .nat count)
    (held : Holds before.refs) : Holds after.refs := by
  change some ({before with refs := before.refs ++ [initial]}, .cell ⟨before.refs.length⟩) = some (after, answer) at actual
  cases actual
  by_cases selected : before.refs.length = 4
  · obtain ⟨count, value⟩ := atCounter selected
    intro foundValue found
    change (before.refs ++ [initial])[4]? = some foundValue at found
    rw [← selected, List.getElem?_concat_length] at found
    cases found
    exact ⟨count, value⟩
  · apply outside (.refMake initial) before _ _ rfl ?_ held
    intro impossible
    have indices := congrArg (fun key : Option RefKey => key.map RefKey.index) impossible
    exact selected (Option.some.inj indices)

/-- Stable source operations and all nonreference administration share the same counter invariant. -/
theorem operation_keeps (total : Nat) (rows : RowTable) (operation : SyncOp)
    (owned : AnswerSlots.Typed.OpAt (QueueWorkersFlow.spec total rows) operation)
    (before after : Stores) (answer : Val) (actual : syncOpStep operation before = some (after, answer))
    (held : Holds before.refs) : Holds after.refs := by
  cases operation
  case refMake | refSet | refGetAndSet | refSetAndGet | refUpdate | refGetAndUpdate
    | refUpdateAndGet | refUpdateSome | refGetAndUpdateSome | refUpdateSomeAndGet
    | refModify | refModifySome => exact source_keeps total rows _ owned before after answer actual held
  case refGet cell =>
    rw [syncOpStep_refGet_refs actual]
    exact held
  all_goals apply outside _ before after answer actual ?_ held
  all_goals intro impossible
  all_goals cases impossible

/-- Actual stored operation wrappers use the same native source writer. -/
theorem thunk_keeps (total : Nat) (rows : RowTable) (view : List (FiberId × ExitV)) (thunk : EffThunk)
    (owned : AnswerSlots.Typed.ThunkAt (QueueWorkersFlow.spec total rows) thunk)
    (before after : Stores) (answer : Val)
    (actual : (interpAt (Programs.queueProgram total) view rows).syncState thunk before = some (after, answer))
    (held : Holds before.refs) : Holds after.refs := by
  obtain ⟨operation, represented, executed⟩ := StoreExecution.native_sync_row (Programs.queueProgram total) view rows
    thunk before after answer actual
  rcases represented with rfl | rfl
  · exact operation_keeps total rows operation owned.2.2 before after answer executed held
  · exact operation_keeps total rows operation owned.2.2 before after answer executed held

/-- The actual initialized current head preserves the counter through allocation and stable execution. -/
theorem current_keeps (total : Nat) (rows : RowTable) (view : List (FiberId × ExitV))
    (world : AnswerSlots.Initialized.World) (kind : AnswerSlots.Initialized.Kind)
    (thunk : EffThunk) (after : Stores) (answer : Val)
    (owned : AnswerSlots.Initialized.CodeAt (QueueWorkersFlow.initializedSpec total rows) world kind (.sync thunk))
    (actual : (interpAt (Programs.queueProgram total) view rows).syncState thunk world.state = some (after, answer))
    (held : Holds world.state.refs) : Holds after.refs := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage =>
    exact (AnswerSlots.Initialized.initial_not_sync (QueueWorkersFlow.initializedSpec total rows)
      world _ _ stage thunk same.symm).elim
  | allocating small stage =>
    cases same
    apply make_keeps _ world.state after answer actual ?_ held
    intro selected
    have indexEq : _ = 4 := stage.2.2.2.2.1.symm.trans selected
    rw [indexEq]
    exact ⟨0, rfl⟩
  | gateAllocating stage =>
    cases same
    apply outside .deferredMake world.state after answer actual ?_ held
    intro impossible
    cases impossible
  | reading phase refs deferred pending =>
    cases same
    rw [syncOpStep_refGet_refs actual]
    exact held
  | stable ready code =>
    cases same
    exact thunk_keeps total rows view thunk code.2 world.state after answer actual held
  | frontier zero phase | yielding phase refs deferred pending | bound first callback | yieldThen phase code => cases same
end Test.Dogfood.Proofs.QueueWorkersCountCell
