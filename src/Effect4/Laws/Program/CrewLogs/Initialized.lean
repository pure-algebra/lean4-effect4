import Effect4.Laws.Program.CrewLogs.Writes
import Effect4.Laws.Program.AnswerSlots.InitializedSync

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: initialized answer flow supplies the actual log writer used by CrewLogs.history.
Consumers: the Workers and QueueWorkers source instances.
Reach: certified root allocations and stable source operations at an actual synchronous head.
The frame-history producer remains a separate premise; this connector supplies no progress.
-/
set_option autoImplicit false
namespace Effect4.Program.CrewLogs
open Effect4 Effect4.Machine Effect4.Program
open AnswerSlots

/-- The concrete source proves its stable writes and the empty initial log values. -/
structure SyncContract (crew : Spec) (spec : Initialized.Spec) : Prop where
  initial : ∀ index, index < spec.initialization.width →
    (spec.initialization.initial index).asList?.getD [] = []
  source : ∀ operation, Typed.OperationSource spec.toSpec operation → ∀ before after value,
    syncOpStep operation before = some (after, value) → SyncChange crew before.refs after.refs (.op operation)

/-- The stable source contract covers writers; the existing heap projection covers all administration. -/
theorem operation_change {crew : Spec} {spec : Initialized.Spec} (contract : SyncContract crew spec)
    (operation : SyncOp) (owned : Typed.OpAt spec.toSpec operation)
    (before after : Stores) (value : Val) (actual : syncOpStep operation before = some (after, value)) :
    SyncChange crew before.refs after.refs (.op operation) := by
  cases operation
  case refMake | refSet | refGetAndSet | refSetAndGet | refUpdate | refGetAndUpdate
    | refUpdateAndGet | refUpdateSome | refGetAndUpdateSome | refUpdateSomeAndGet
    | refModify | refModifySome => exact contract.source _ owned before after value actual
  case refGet cell =>
    exact .inl (by rw [syncOpStep_refGet_refs actual])
  all_goals apply outside_change crew _ before after value actual
  all_goals intro impossible
  all_goals cases impossible

/-- Stored wrappers use the same native operation and acquired-source permission. -/
theorem thunk_change {crew : Spec} {spec : Initialized.Spec} (contract : SyncContract crew spec)
    (completed : List (FiberId × ExitV)) (thunk : EffThunk) (owned : Typed.ThunkAt spec.toSpec thunk)
    (before after : Stores) (value : Val)
    (actual : (interpAt spec.root completed spec.table).syncState thunk before = some (after, value)) :
    SyncChange crew before.refs after.refs thunk := by
  obtain ⟨operation, represented, executed⟩ := StoreExecution.native_sync_row spec.root completed spec.table
    thunk before after value actual
  rcases represented with rfl | rfl
  · exact operation_change contract operation owned.2.2 before after value executed
  · exact (operation_change contract operation owned.2.2 before after value executed).stored

/-- Every initialized current synchronous head supplies the one shared log observation. -/
theorem current_change {crew : Spec} {spec : Initialized.Spec} (contract : SyncContract crew spec)
    (completed : List (FiberId × ExitV)) (world : Initialized.World)
    (kind : Initialized.Kind) (thunk : EffThunk) (after : Stores) (value : Val)
    (owned : Initialized.CodeAt spec world kind (.sync thunk))
    (actual : (interpAt spec.root completed spec.table).syncState thunk world.state = some (after, value)) :
    SyncChange crew world.state.refs after.refs thunk := by
  generalize same : Prim.sync thunk = program at owned
  cases owned with
  | success good | failure phase => cases same
  | initial stage => exact (Initialized.initial_not_sync spec world _ _ stage thunk same.symm).elim
  | allocating small stage =>
    cases same
    exact make_change crew _ (contract.initial _ small) world.state after value actual
  | gateAllocating stage =>
    cases same
    change some ({world.state with deferreds := world.state.deferreds.make.2}, .promise world.state.deferreds.make.1) =
      some (after, value) at actual
    cases actual
    exact .inl rfl
  | reading phase refs deferred pending =>
    cases same
    exact .inl (by rw [syncOpStep_refGet_refs actual])
  | stable ready held =>
    cases same
    exact thunk_change contract completed thunk held.2 world.state after value actual
  | frontier zero phase | yielding phase refs deferred pending | bound first callback | yieldThen phase held => cases same

/-- The actual frame-history producer supplies only its current code certificate at the looked-up owner. -/
theorem writes_of_current {crew : Spec} {spec : Initialized.Spec} (contract : SyncContract crew spec)
    (m : NativeMachine)
    (current : ∀ id fiber, m.fiber? id = some fiber → ∃ kind,
      Initialized.CodeAt spec ⟨fiber.id, m.state⟩ kind fiber.frame.current) :
    Writes crew spec.root spec.table m := by
  intro id fiber found thunk after value selected actual
  obtain ⟨kind, owned⟩ := current id fiber found
  rw [selected] at owned
  exact current_change contract m.completedExits ⟨fiber.id, m.state⟩ kind thunk after value owned actual
end Effect4.Program.CrewLogs
