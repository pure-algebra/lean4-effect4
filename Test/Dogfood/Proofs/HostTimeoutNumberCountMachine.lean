import Test.Dogfood.Proofs.HostTimeoutNumberPassive
import Test.Dogfood.Proofs.HostTimeoutNumberRootTransitions

/-!
Concepts: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: the actual counter write advances the entire numeric machine assertion together.
Consumer: the count branch of the coupled native producer for both Timeout goals.
Reach: the actual unique active attempt, passive siblings, actual unparked count loop, and stored replies.
Limit: the race protocol must establish the unique active-attempt census and subsequent queue demands.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberCountMachine
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutState HostTimeoutNumberConfiguration HostTimeoutNumberConfigurationTransport
open HostTimeoutNumberPassive HostTimeoutNumberPhase

/-- An installed actual writer replaces its own row in the post-operation store. -/
def installed (machine : Effect4.Program.NativeMachine) (state : Stores)
    (fiber : Effect4.Program.SourceScope.SourceFiber) : Effect4.Program.NativeMachine :=
  ({machine with state}).update fiber

/-- A reply to the active unparked writer is stale; every passive reply retains its actual saved suffix. -/
theorem reply_store (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (before after : Effect4.Program.SourceScope.SourceFiber) (state : Stores)
    (census : OnlyAttempt world before.id context) (found : machine.fiber? before.id = some before)
    (key : after.id = before.id) (unparked : after.parked = .notParked)
    (id : FiberId) (token : Nat) (code : NCode) (held : ReplyAt world machine id token code) :
    ReplyAt world (installed machine state after) id token code := by
  intro fiber actual live parked role assigned
  by_cases same : id = before.id
  · subst id
    have self : (installed machine state after).fiber? before.id = some after := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at actual
    cases actual
    rw [unparked] at parked
    cases parked
  · have other : id ≠ after.id := by intro equal; exact same (equal.trans key)
    have old : machine.fiber? id = some fiber := by
      unfold installed at actual
      rw [RunMachine.fiber?_update_other after {machine with state} id other] at actual
      exact actual
    exact frame_store machine _ role _ (other_passive world before.id context id role census assigned same)
      (held fiber old live parked role assigned)

/-- An actual active-writer replacement retains every passive fiber and stored reply snapshot. -/
theorem configuration_store (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (before after : Effect4.Program.SourceScope.SourceFiber) (state : Stores) (phase : Phase)
    (census : OnlyAttempt world before.id context) (found : machine.fiber? before.id = some before)
    (assigned : (before.id, Role.pending context) ∈ world.roles)
    (key : after.id = before.id) (unparked : after.parked = .notParked)
    (dispatcher : after.dispatcher = before.dispatcher) (heap : state.refs = phase.heap)
    (held : Configuration world machine) (active : FiberAt (installed machine state after) (.pending context) after) :
    Configuration {world with phase} (installed machine state after) := by
  constructor
  · exact heap
  · intro fiber member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal]
    change ∃ role, ((if old.id = after.id then after else old).id, role) ∈ world.roles ∧
      FiberAt (installed machine state after) role (if old.id = after.id then after else old)
    split
    · exact ⟨.pending context, by rw [key]; exact assigned, active⟩
    · rename_i different
      obtain ⟨role, roleAt, good⟩ := held.roles old present
      have other : old.id ≠ before.id := by intro equal; exact different (equal.trans key.symm)
      exact ⟨role, roleAt, fiber_store machine _ role old
        (other_passive world before.id context old.id role census roleAt other) good⟩
  · exact held.unique
  · intro fiber member bucket stored
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal] at stored
    change bucket ∈ (if old.id = after.id then after else old).dispatcher.buckets at stored
    split at stored
    · rw [dispatcher] at stored
      exact snapshot_replies world machine _ bucket.tasks
        (reply_store world machine context before after state census found key unparked)
        (held.dispatchers before (RunMachine.mem_of_fiber? found) bucket stored)
    · exact snapshot_replies world machine _ bucket.tasks
        (reply_store world machine context before after state census found key unparked)
        (held.dispatchers old present bucket stored)

/-- A real count increment separates the entered heap from its predecessor heap. -/
theorem counted_heap_ne (context : CountContext) : context.entered.heap ≠ context.before.heap := by
  intro equal
  have cell := congrArg (fun (heap : RefHeap) => heap[0]?) equal
  change some (Val.nat (context.before.count + 1)) = some (.nat context.before.count) at cell
  have number := congrArg (fun value : Val => match value with | .nat n => n | _ => 0) (Option.some.inj cell)
  change context.before.count + 1 = context.before.count at number
  omega

/-- The actual count answer retains the full attempt role, including execution and interruption permissions. -/
theorem counted_fiber (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (held : FiberAt machine (.pending context) fiber) (live : fiber.exit = none)
    (heap : HostTimeoutNumberPhaseFlow.At context.before machine.state)
    (_current : fiber.frame.current = context.write)
    (stack : fiber.frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
      .onExit context.bound (.fin context.point) false]) (_ready : CountReady context fiber yielding) :
    let state := {machine.state with refs := context.entered.heap}
    let after := {countOp fiber with frame := {fiber.frame with current := .success .unit}}
    FiberAt (installed machine state after) (.pending context) after := by
  have installedFin : CountInstalled context fiber.frame := by
    change _ ∈ fiber.frame.stack
    rw [stack]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have running := held.pendingRunning context rfl heap installedFin
  constructor
  · refine ⟨HostTimeoutNumberSourceWrites.counted_frame context fiber.frame stack, ?_⟩
    exact counted_frame_uniform context _ fiber.frame rfl stack
  · intro selected published
    change fiber.exit = some selected at published
    rw [live] at published
    cases published
  · intro impossible
    cases impossible
  · exact held.recorded
  · intro cause clean alive idle interruptible
    change fiber.running = false at idle
    rw [running] at idle
    cases idle
  · intro next same afterHeap installedNext
    cases same
    exact False.elim (counted_heap_ne context afterHeap)

  · intro next same afterHeap interruptible
    cases same
    exact installedFin

  · intro next same masked
    exact held.pendingDeferred next same masked

/-- The actual count write advances the entire numeric machine and its stored reply tasks. -/
theorem count_machine (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool)
    (census : OnlyAttempt world fiber.id context) (found : machine.fiber? fiber.id = some fiber)
    (assigned : (fiber.id, Role.pending context) ∈ world.roles) (held : Configuration world machine)
    (live : fiber.exit = none) (heap : HostTimeoutNumberPhaseFlow.At context.before machine.state)
    (current : fiber.frame.current = context.write)
    (stack : fiber.frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
      .onExit context.bound (.fin context.point) false]) (ready : CountReady context fiber yielding) :
    let state := {machine.state with refs := context.entered.heap}
    let after := {countOp fiber with frame := {fiber.frame with current := .success .unit}}
    Configuration {world with phase := context.entered} (installed machine state after) := by
  let state : Stores := {machine.state with refs := context.entered.heap}
  let after : SourceScope.SourceFiber := {countOp fiber with frame := {fiber.frame with current := .success .unit}}
  exact configuration_store world machine context fiber after state context.entered census found assigned rfl
    ready.2.2 rfl rfl held (counted_fiber machine context fiber yielding
      (held.lookup world machine fiber.id (.pending context) assigned fiber found) live heap current stack ready)

end Test.Dogfood.Proofs.HostTimeoutNumberCountMachine
