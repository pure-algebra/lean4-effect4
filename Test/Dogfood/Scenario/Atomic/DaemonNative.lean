import Test.Dogfood.Scenario.Atomic.DaemonHead
import Test.Dogfood.Scenario.Atomic.StageHeap
import Effect4.Laws.Machine.StoresLaws

/-!
Concept: store-typing R4.
Consumer: the Atomic daemon primitive evaluator in the actual command/history invariant.
The actual refill and timer cancellation preserve the same stage world and heap assertion.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.DaemonGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Only a window refill or timer cancellation is a daemon synchronous primitive. -/
inductive SyncAt : EffThunk → Prop
  | refill (env : List Val) (length : env.length = 5) :
      SyncAt (.op (.refUpdate ⟨0⟩ (Store.refillAt 5) env))
  | cancel (waiter : FiberId) (token : Nat) : SyncAt (.store (.op (.sleepCancel waiter token)))

/-- The actual daemon source and its wrappers expose no other synchronous store operation. -/
theorem sync_shape (root : NativeEff) (table : RowTable) (code : NCode)
    (held : CodeAt root table code) (thunk : EffThunk) (equal : code = .sync thunk) : SyncAt thunk := by
  cases held with
  | @entry point owned =>
    rw [SourceScope.resolve_at _ _ _ owned.1] at equal
    cases amount : point.fuel with
    | zero => simp only [Agreement.compileEff_at_zero _ amount] at equal; cases equal
    | succ fuel => simp only [DaemonSource.program, compileEff, amount] at equal; cases equal
  | @body point owned =>
    rw [SourceScope.resolve_at _ _ _ owned.1] at equal
    cases amount : point.fuel with
    | zero => simp only [Agreement.compileEff_at_zero _ amount] at equal; cases equal
    | succ fuel => simp only [DaemonSource.body, compileEff, amount] at equal; cases equal
  | @update point owned =>
    rw [SourceScope.resolve_at _ _ _ owned.1] at equal
    cases amount : point.fuel with
    | zero => simp only [Agreement.compileEff_at_zero _ amount] at equal; cases equal
    | succ fuel =>
      have captured : point.env[0]? = some (.cell ⟨0⟩) := owned.2.2.read 0 (by decide)
      simp only [compileEff, amount, NativeOp.kind, evalTerm, captured, NativeOp.syncOpOf] at equal
      cases equal
      exact .refill _ owned.2.1
  | refill length =>
    cases equal
    exact .refill _ length
  | cancelClock waiter token => cases equal; exact .cancel waiter token
  | join target mode => cases equal
  | awaitAll targets => cases equal
  | interruptAll targets who => cases equal
  | dropObservers token => cases equal
  | frontier zero => cases equal
  | success value => cases equal
  | failure cause => cases equal
  | loop owned cursor => cases equal
  | sleep => cases equal
  | constant first next => cases equal
  | pause priority => cases equal
  | bound first callback => cases equal

/-- The daemon's actual native actions only interrupt or remove observer tokens. -/
theorem action_shape (root : NativeEff) (table : RowTable) (thunk : EffThunk)
    (held : CodeAt root table (.withFiber thunk)) :
    (∃ targets who, thunk = .store (.act (.interruptAll targets who))) ∨
      (∃ token, thunk = .store (.act (.dropObservers token))) := by
  generalize equal : Prim.withFiber thunk = code at held
  cases held with
  | @entry point owned =>
    rw [SourceScope.resolve_at _ _ _ owned.1] at equal
    cases amount : point.fuel with
    | zero => simp only [Agreement.compileEff_at_zero _ amount] at equal; cases equal
    | succ fuel => simp only [DaemonSource.program, compileEff, amount] at equal; cases equal
  | @body point owned =>
    rw [SourceScope.resolve_at _ _ _ owned.1] at equal
    cases amount : point.fuel with
    | zero => simp only [Agreement.compileEff_at_zero _ amount] at equal; cases equal
    | succ fuel => simp only [DaemonSource.body, compileEff, amount] at equal; cases equal
  | @update point owned =>
    rw [SourceScope.resolve_at _ _ _ owned.1] at equal
    cases amount : point.fuel with
    | zero => simp only [Agreement.compileEff_at_zero _ amount] at equal; cases equal
    | succ fuel =>
      have captured : point.env[0]? = some (.cell ⟨0⟩) := owned.2.2.read 0 (by decide)
      simp only [compileEff, amount, NativeOp.kind, evalTerm, captured, NativeOp.syncOpOf] at equal
      cases equal
  | interruptAll targets who => cases equal; exact .inl ⟨targets, who, rfl⟩
  | dropObservers token => cases equal; exact .inr ⟨token, rfl⟩
  | success value => cases equal
  | failure cause => cases equal
  | loop owned cursor => cases equal
  | frontier zero => cases equal
  | sleep => cases equal
  | refill length => cases equal
  | cancelClock waiter token => cases equal
  | join target mode => cases equal
  | awaitAll targets => cases equal
  | constant first next => cases equal
  | pause priority => cases equal
  | bound first callback => cases equal

/-- The actual daemon synchronous primitive retains the shop heap at the same stage world. -/
theorem sync_heap (root : NativeEff) (table : RowTable) (world : StageWorld.World) (state : Stores)
    (thunk : EffThunk) (code : CodeAt root table (.sync thunk)) (heap : HeapAt world state) :
    ∃ after answer, (interpOf root table).syncState thunk state = some (after, answer) ∧ HeapAt world after := by
  have shape := sync_shape root table _ code thunk rfl
  cases shape with
  | refill env length =>
    obtain ⟨after, actual, heapNext⟩ := refill_heap world state env heap
    rw [length] at actual
    exact ⟨after, .unit, actual, heapNext⟩
  | cancel waiter token =>
    refine ⟨{state with timers := state.timers.cancel waiter token}, .unit,
      syncOpStep_sleepCancel state waiter token, ?_⟩
    exact ⟨heap.witness⟩
end Test.Dogfood.Scenario.Atomic.DaemonGraph
