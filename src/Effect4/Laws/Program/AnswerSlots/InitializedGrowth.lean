import Effect4.Laws.Program.AnswerSlots.InitializedCounts
import Effect4.Laws.Program.NativeStatePreservation

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: actual native iterations retain the allocation counts needed by every nonacting saved frame.
Reach: all native synchronous operations, asynchronous registration and administrative scoped operations.
Limit: frame permission and births use their separate initialized producers.
Consumer: actual other-row Flows and the crew log-history command driver.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

def Bounds (refs deferred : Nat) (state : Stores) : Prop :=
  refs ≤ state.refs.length ∧ deferred ≤ state.deferreds.cells.length

theorem bounds_counts (refs deferred : Nat) (state next : Stores)
    (held : Bounds refs deferred state) (counts : Counts state.refs.length state.deferreds.cells.length next) :
    Bounds refs deferred next := by
  unfold Bounds
  rw [counts.1, counts.2]
  exact held

/-- Actual native store hooks never shrink either allocation store. -/
theorem growth_hooks (spec : Spec) (view : List (FiberId × ExitV)) (refs deferred : Nat) :
    StatePreservation.Hooks (interpAt spec.root view spec.table) (Bounds refs deferred) where
  sync := by
    intro thunk state next value held ran
    have growth := sync_future spec view ⟨⟨0⟩, state⟩ thunk next value ran
    exact ⟨Nat.le_trans held.1 growth.2.1, Nat.le_trans held.2 growth.2.2⟩
  async := by
    intro name owner token state held
    exact bounds_counts refs deferred state _ held (register_counts spec view ⟨owner, state⟩ name owner token)
  link := by
    intro mode scope owner state next key held ran
    have counts := (count_hooks spec view state.refs.length state.deferreds.cells.length).link mode scope owner state next key ⟨rfl, rfl⟩ ran
    exact bounds_counts refs deferred state next held counts
  close := by
    intro scope exit flag owner state next code held ran
    exact bounds_counts refs deferred state next held (close_counts spec view scope exit flag owner state next code ran)
  drop := by
    intro scope key state next held ran
    have counts := (count_hooks spec view state.refs.length state.deferreds.cells.length).drop scope key state next ⟨rfl, rfl⟩ ran
    exact bounds_counts refs deferred state next held counts
  due := by
    intro state held
    exact bounds_counts refs deferred state _ held
      ((count_hooks spec view state.refs.length state.deferreds.cells.length).due state ⟨rfl, rfl⟩)
  wake := by
    intro key phase state held
    exact bounds_counts refs deferred state _ held
      ((count_hooks spec view state.refs.length state.deferreds.cells.length).wake key phase state ⟨rfl, rfl⟩)

/-- The native evaluator retains arbitrary lower bounds on both allocation counts. -/
theorem native_bounds (spec : Spec) (refs deferred : Nat) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : Bounds refs deferred machine.state) :
    Bounds refs deferred (evaluateNative spec.root machine fiber yielding spec.table).machine.state := by
  apply NativeStatePreservation.native spec.root spec.table (Bounds refs deferred)
  · intro view machine fiber yielding good
    exact StatePreservation.primitive (interpAt spec.root view spec.table) (Bounds refs deferred)
      (growth_hooks spec view refs deferred) machine fiber yielding good
  · intro machine fiber yielding good
    exact StatePreservation.primitive (interpAt spec.root machine.completedExits []) (Bounds refs deferred)
      (growth_hooks {spec with table := []} machine.completedExits refs deferred) machine fiber yielding good
  · intro state good
    exact good
  · intro scope exit flag state next program good ran
    exact bounds_counts refs deferred state next good (unsafe_counts scope exit flag state next program ran)
  · exact held

/-- Actual native evaluation grows only the two allocation counts used by initialized classes. -/
theorem native_growth (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    Bounds machine.state.refs.length machine.state.deferreds.cells.length
      (evaluateNative spec.root machine fiber yielding spec.table).machine.state :=
  native_bounds spec _ _ machine fiber yielding ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- The shared charged iteration transports the same store lower bounds. -/
theorem iteration_bounds (spec : Spec) (refs deferred : Nat) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (held : Bounds refs deferred machine.state) :
    Bounds refs deferred
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine.state :=
  StatePreservation.iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table)
    (Bounds refs deferred) (native_bounds spec refs deferred) machine fiber yielding held

/-- The actual iteration leaves enough cells for every old nonacting frame. -/
theorem iteration_growth (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) :
    Bounds machine.state.refs.length machine.state.deferreds.cells.length
      (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine.state :=
  iteration_bounds spec _ _ machine fiber yielding ⟨Nat.le_refl _, Nat.le_refl _⟩
end Effect4.Program.AnswerSlots.Initialized
