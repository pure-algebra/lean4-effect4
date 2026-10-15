import Test.Dogfood.Scenario.RootCells
import Test.Dogfood.Scenario.Atomic.RootBindings
import Effect4.Laws.Program.AnswerSlots.AllocationIteration

/-!
Concept: store-typing R4, serving Atomic.Store.shop_stages.
Question: actual prefix cuts retain waiting request stages before any request fiber exists.
Reach: the common exact initializer heap and its exclusive root frame ownership.
Consumer: the early branch and source-entry branch of the coupled Atomic stage invariant.
This observation reader does not assert an admitted machine history or request progress.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Atomic.Initialization
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.AnswerSlots
open Effect4.Program.AnswerSlots.AllocationAdapter

/-- Before source entry, initialized frame ownership excludes every request identity. -/
theorem root_only_absent (machine : NativeMachine)
    (owners : ∀ fiber ∈ machine.fibers, fiber.id = ⟨0⟩) (id : FiberId) (different : id ≠ ⟨0⟩) :
    machine.fiber? id = none := by
  cases found : machine.fiber? id with
  | none => rfl
  | some fiber =>
    have owner := owners fiber (RunMachine.mem_of_fiber? found)
    have key := RunMachine.id_of_fiber? found
    exact (different (key.symm.trans owner)).elim

/-- The common pending frame graph supplies that root ownership without a second source walk. -/
theorem pending_absent (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (machine : NativeMachine)
    (held : FramesAt (RootCells.atomicAdapter built accepted) fragment false machine)
    (id : FiberId) (different : id ≠ ⟨0⟩) : machine.fiber? id = none :=
  root_only_absent machine (fun fiber member => FrameAt.pending_owner (RootCells.atomicAdapter built accepted) fragment _ fiber.frame (held fiber member) rfl) id different

/-- No request exits before the actual initializer hands control to the root body. -/
theorem pending_decisions (machine : NativeMachine)
    (owners : ∀ fiber ∈ machine.fibers, fiber.id = ⟨0⟩) :
    requestFibers.map (fun fiber => outcomeOf ((machine.fiber? fiber).bind RunFiber.exit)) =
      [.pending, .pending, .pending, .pending, .pending, .pending] := by
  change [outcomeOf ((machine.fiber? ⟨2⟩).bind RunFiber.exit),
    outcomeOf ((machine.fiber? ⟨3⟩).bind RunFiber.exit),
    outcomeOf ((machine.fiber? ⟨4⟩).bind RunFiber.exit),
    outcomeOf ((machine.fiber? ⟨5⟩).bind RunFiber.exit),
    outcomeOf ((machine.fiber? ⟨6⟩).bind RunFiber.exit),
    outcomeOf ((machine.fiber? ⟨7⟩).bind RunFiber.exit)] = _
  rw [root_only_absent machine owners ⟨2⟩ (by decide), root_only_absent machine owners ⟨3⟩ (by decide),
    root_only_absent machine owners ⟨4⟩ (by decide), root_only_absent machine owners ⟨5⟩ (by decide),
    root_only_absent machine owners ⟨6⟩ (by decide), root_only_absent machine owners ⟨7⟩ (by decide)]
  rfl

/-- Partial exact initialization exposes zero admissions, zero rejections and no deposit history. -/
theorem prefix_counts (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (machine : NativeMachine) (heap : HeapPrefix (RootCells.atomicAdapter built accepted) machine.state) :
    (Store.observeM machine).admitted = 0 ∧ (Store.observeM machine).rejected = 0 ∧
      (Store.observeM machine).deposits = [] := by
  have bound : machine.state.refs.length ≤ 3 := heap.2.1
  have content : machine.state.refs = (Initialization.values RootCells.atomic 3).take machine.state.refs.length := by
    exact heap.1.trans (Initialization.values_take (RootCells.atomicBuilt built accepted) _ heap.2.1)
  rw [RootCells.atomic_values] at content
  have index : machine.state.refs.length = 0 ∨ machine.state.refs.length = 1 ∨
      machine.state.refs.length = 2 ∨ machine.state.refs.length = 3 := by omega
  rcases index with count | count | count | count
  all_goals rw [count] at content
  all_goals simp only [Store.observeM, Observation.admitted, Observation.rejected, Observation.deposits, content]
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- Every exact pending prefix cut satisfies the original stage observation with all requests waiting. -/
theorem pending_stages (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (fragment : SourceScope.Fragment built.program) (machine : NativeMachine)
    (held : FramesAt (RootCells.atomicAdapter built accepted) fragment false machine)
    (heap : HeapPrefix (RootCells.atomicAdapter built accepted) machine.state) :
    Store.StagesFit (fun _ => .waiting) (Store.observeM machine) := by
  have owners : ∀ fiber ∈ machine.fibers, fiber.id = ⟨0⟩ :=
    fun fiber member => FrameAt.pending_owner (RootCells.atomicAdapter built accepted) fragment _ fiber.frame (held fiber member) rfl
  have decisions := pending_decisions machine owners
  obtain ⟨admitted, rejected, deposits⟩ := prefix_counts built accepted machine heap
  refine ⟨admitted, rejected, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro id member
    rw [deposits]
    rfl
  · rw [deposits]
    rfl
  · rw [deposits]
    rfl
  · intro pair member
    change pair ∈ ((requestFibers.map (fun fiber => outcomeOf ((machine.fiber? fiber).bind RunFiber.exit))).zip requests) at member
    rw [decisions] at member
    simp only [requests, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨(fun impossible => nomatch impossible), (fun impossible => nomatch impossible)⟩
  · change (requestFibers.map (fun fiber => outcomeOf ((machine.fiber? fiber).bind RunFiber.exit))).length = 6
    rw [decisions]
    rfl
  · change (requestFibers.map (fun fiber => outcomeOf ((machine.fiber? fiber).bind RunFiber.exit)))[1]? = some .failedBehind → _
    rw [decisions]
    intro impossible
    cases impossible

end Test.Dogfood.Scenario.Atomic.Initialization
