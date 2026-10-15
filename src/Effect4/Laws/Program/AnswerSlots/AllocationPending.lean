import Effect4.Laws.Program.AnswerSlots.AllocationWaits

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Question: actual initialization admits only allocation, ignored replies and ordinary frame administration before entry.
Reach: the existing CodeAt judgment with the actual source entry branch explicit.
Consumer: the common pending-prefix native producer and Atomic's coupled stage history.
The explicit entry branch routes execution to the application's numeric transition.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- Actual prefix heads cannot perform fiber actions, register async work or import a park before entry. -/
theorem pending_ordinary_or_entry (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (program : NCode) (owned : CodeAt spec world kind program)
    (pending : world.entered = false) :
    ((interpAt spec.root view spec.table).parkOf program = none ∧
      (∀ thunk, program ≠ .withFiber thunk) ∧ (∀ name signal cancel, program ≠ .async name signal cancel)) ∨
    ∃ point, kind = .stable spec.stable.rootKind ∧ program = resolve spec.root point ∧ Entry spec world point := by
  cases owned with
  | initial stage active =>
    rcases initial_shape spec world _ _ stage active with ⟨body, name, same⟩ | same | ⟨cause, same⟩
    all_goals rw [same]
    all_goals exact .inl ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal)⟩
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready owned => exact (pending_not_ready spec world pending ready).elim
  | success good | failure phase | allocating small stage | gateAllocating stage available
    | frontier zero phase | yielding phase refs deferred missing contents entered
    | reading phase refs deferred missing contents entered
    | yieldThen phase next missing =>
    exact .inl ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal)⟩

end Effect4.Program.AnswerSlots.AllocationAdapter
