import Effect4.Laws.Program.AnswerSlots.AllocationWaits
import Effect4.Laws.Program.AnswerSlots.AllocationDeferredQuiet

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
theorem pending_metadata_or_entry (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (program : NCode) (owned : CodeAt spec world kind program)
    (pending : world.entered = false) :
    ((interpAt spec.root view spec.table).parkOf program = none ∧
      (∀ thunk, program ≠ .withFiber thunk) ∧ (∀ name signal cancel, program ≠ .async name signal cancel) ∧
      (∀ thunk state value, program = .sync thunk →
        (interpAt spec.root view spec.table).syncState thunk world.state = some (state, value) →
        DeferredQuiet world.state.deferreds → DeferredQuiet state.deferreds)) ∨
    ∃ point, kind = .stable spec.stable.rootKind ∧ program = resolve spec.root point ∧ Entry spec world point := by
  cases owned with
  | initial stage active =>
    rcases initial_shape spec world _ _ stage active with ⟨body, name, same⟩ | same | ⟨cause, same⟩
    all_goals rw [same]
    all_goals exact .inl ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal),
      (by intro thunk state value equal; cases equal)⟩
  | entered fragment entry => exact .inr ⟨_, rfl, rfl, entry⟩
  | stable ready owned => exact (pending_not_ready spec world pending ready).elim
  | @allocating index point small stage =>
    apply Or.inl
    refine ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal), ?_⟩
    intro thunk state value equal ran quiet
    cases equal
    obtain ⟨key, written⟩ := Initialization.actual spec.initialization index world.state state value ran
    subst state
    exact quiet
  | gateAllocating stage available =>
    apply Or.inl
    refine ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal), ?_⟩
    intro thunk state value equal ran quiet
    cases equal
    change syncOpStep .deferredMake world.state = some (state, value) at ran
    rw [syncOpStep_deferredMake] at ran
    cases ran
    refine ⟨quiet.1, ?_⟩
    intro cell member
    rcases List.mem_append.mp member with before | fresh
    · exact quiet.2 cell before
    · cases List.mem_singleton.mp fresh
      rfl
  | @reading refs deferred cell phase refsEq deferredEq missing contents entered =>
    apply Or.inl
    refine ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal), ?_⟩
    intro thunk state value equal ran quiet
    cases equal
    change syncOpStep (.refGet cell) world.state = some (state, value) at ran
    cases peek : refPeek world.state.refs cell with
    | none =>
      simp only [syncOpStep, refStep, peek, Option.map_none] at ran
      cases ran
    | some answer =>
      simp only [syncOpStep, refStep, peek, Option.map_some] at ran
      cases ran
      exact quiet
  | success good | failure phase | frontier zero phase
    | yielding phase refs deferred missing contents entered | yieldThen phase next missing =>
    exact .inl ⟨rfl, (by intro thunk equal; cases equal), (by intro name signal cancel equal; cases equal),
      (by intro thunk state value equal; cases equal)⟩

/-- The original ordinary-head interface reads the same actual source classifier. -/
theorem pending_ordinary_or_entry (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (kind : Kind spec.stable.Kind) (program : NCode) (owned : CodeAt spec world kind program)
    (pending : world.entered = false) :
    ((interpAt spec.root view spec.table).parkOf program = none ∧
      (∀ thunk, program ≠ .withFiber thunk) ∧ (∀ name signal cancel, program ≠ .async name signal cancel)) ∨
    ∃ point, kind = .stable spec.stable.rootKind ∧ program = resolve spec.root point ∧ Entry spec world point := by
  rcases pending_metadata_or_entry spec view world kind program owned pending with ordinary | entry
  · exact .inl ⟨ordinary.1, ordinary.2.1, ordinary.2.2.1⟩
  · exact .inr entry

end Effect4.Program.AnswerSlots.AllocationAdapter
