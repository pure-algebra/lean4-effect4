import Test.Dogfood.Proofs.HostTimeoutNumberConfigurationInterrupt
import Effect4.Laws.Machine.Ledger

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: actual metadata edits retain the numeric machine and reply assertions.
Consumer: the contextual message producer and fixed administrative command cases for Timeout.
Reach: the same actual store, completed-exit view, and retained fibers.
Limit: replacing a fiber still requires actual lookup and pending-command transport.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberConfigurationTransport
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutNumberConfiguration HostTimeoutState

/-- Numeric frame assertions depend on the actual store and completed-exit view. -/
theorem frame_machine (before after : Effect4.Program.NativeMachine) (role : Role)
    (frame : HostTimeoutFrames.NativeFrame) (state : after.state = before.state)
    (_view : after.completedExits = before.completedExits) (held : FrameAt before role frame) :
    FrameAt after role frame := by
  unfold HostTimeoutNumberConfiguration.FrameAt
  rw [state]
  exact held

/-- Numeric published exits use the same actual store and completed-exit view. -/
theorem exit_machine (before after : Effect4.Program.NativeMachine) (role : Role) (exit : ExitV)
    (state : after.state = before.state) (view : after.completedExits = before.completedExits)
    (held : ExitAt before role exit) : ExitAt after role exit := by
  unfold ExitAt
  rw [state, view]
  exact held

/-- A retained fiber transports all numeric permissions to the same store and completed-exit view. -/
theorem fiber_machine (before after : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (state : after.state = before.state)
    (view : after.completedExits = before.completedExits) (held : FiberAt before role fiber) :
    FiberAt after role fiber := by
  constructor
  · exact frame_machine before after role fiber.frame state view held.frame
  · intro selected found
    exact exit_machine before after role selected state view (held.exit selected found)
  · exact held.retired
  · exact held.recorded
  · intro cause clean live idle interruptible
    exact frame_machine before after role _ state view (held.immediate cause clean live idle interruptible)
  · intro context same heap installed
    apply held.pendingRunning context same _ installed
    change before.state.refs = context.before.heap
    change after.state.refs = context.before.heap at heap
    rw [state] at heap
    exact heap

  · intro context same heap interruptible
    apply held.pendingCustody context same _ interruptible
    change before.state.refs = context.entered.heap
    change after.state.refs = context.entered.heap at heap
    rw [state] at heap
    exact heap
  · exact held.pendingDeferred

/-- A reply reuses the actual lookup when fibers, store, and completed exits stay the same. -/
theorem reply_fields (world : HostTimeoutNumberConfiguration.World) (before after : Effect4.Program.NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) (fibers : after.fibers = before.fibers)
    (state : after.state = before.state) (view : after.completedExits = before.completedExits)
    (held : ReplyAt world before id token code) : ReplyAt world after id token code := by
  intro fiber found live parked role assigned
  have old : before.fiber? id = some fiber := by
    simpa only [RunMachine.fiber?, fibers] using found
  exact frame_machine before after role _ state view (held fiber old live parked role assigned)

/-- Detached tasks retain their actual reply obligations through metadata edits. -/
theorem snapshot_fields (world : HostTimeoutNumberConfiguration.World) (before after : Effect4.Program.NativeMachine) (tasks : List NTask)
    (fibers : after.fibers = before.fibers) (state : after.state = before.state)
    (view : after.completedExits = before.completedExits) (held : Snapshot world before tasks) :
    Snapshot world after tasks := by
  intro task member
  have taskGood := held task member
  cases task with
  | resume id token code => exact reply_fields world before after id token code fibers state view taskGood
  | start id => trivial
  | wake id token => exact taskGood

/-- Metadata edits retain the full numeric machine assertion and its stored reply tasks. -/
theorem configuration_fields (world : HostTimeoutNumberConfiguration.World) (before after : Effect4.Program.NativeMachine)
    (fibers : after.fibers = before.fibers) (state : after.state = before.state)
    (view : after.completedExits = before.completedExits) (held : Configuration world before) :
    Configuration world after := by
  constructor
  · rw [state]
    exact held.heap
  · intro fiber member
    obtain ⟨role, assigned, good⟩ := held.roles fiber (fibers ▸ member)
    exact ⟨role, assigned, fiber_machine before after role fiber state view good⟩
  · exact held.unique
  · intro fiber member bucket stored
    exact snapshot_fields world before after bucket.tasks fibers state view
      (held.dispatchers fiber (fibers ▸ member) bucket stored)

  · exact held.pendingPhase

/-- Replacing the actual unique addressed row with the same id and exit retains the completed-exit view. -/
theorem update_view (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber)
    (found : machine.fiber? before.id = some before)
    (unique : (machine.fibers.map (·.id)).Nodup)
    (key : after.id = before.id) (exit : after.exit = before.exit) :
    (machine.update after).completedExits = machine.completedExits := by
  unfold RunMachine.completedExits RunMachine.update
  rw [List.filterMap_map]
  apply (List.map_inj_right (f := some) (fun _ _ equal => Option.some.inj equal)).mp
  rw [List.map_filterMap_some_eq_filter_map_isSome, List.map_filterMap_some_eq_filter_map_isSome]
  congr 1
  apply List.map_congr_left
  intro old member
  dsimp only [Function.comp_apply]
  split
  · rename_i same
    have lookup := Effect4.Machine.fiber_lookup_of_mem_nodup machine unique old member
    have oldKey : old.id = before.id := same.trans key
    rw [oldKey, found] at lookup
    have equal : before = old := Option.some.inj lookup
    rw [← equal, key, exit]
  · rfl

/-- The actual interruption changes neither completed exits nor their order. -/
theorem interrupt_view (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (found : machine.fiber? fiber.id = some fiber)
    (unique : (machine.fibers.map (·.id)).Nodup) :
    (machine.update (interruptWithCause cause fiber).1).completedExits = machine.completedExits :=
  update_view machine fiber _ found unique (StackLedger.interruptWithCause_key cause fiber)
    (HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause).1


/-- A reply uses the actual replacement row and the same saved suffix when its guard still matches. -/
theorem reply_update (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber) (id : FiberId) (token : Nat) (code : NCode)
    (found : machine.fiber? before.id = some before) (key : after.id = before.id)
    (exit : after.exit = before.exit) (stack : after.frame.stack = before.frame.stack)
    (parked : ∀ guard, after.parked = .withGuard guard → before.parked = .withGuard guard)
    (view : (machine.update after).completedExits = machine.completedExits)
    (held : ReplyAt world machine id token code) : ReplyAt world (machine.update after) id token code := by
  intro fiber selected live waiting role assigned
  by_cases same : id = before.id
  · subst id
    have self : (machine.update after).fiber? before.id = some after := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at selected
    cases selected
    exact frame_machine machine (machine.update after) role _ rfl view
      (HostTimeoutNumberConfigurationInterrupt.frame_fields machine role
        {before.frame with current := code} {after.frame with current := code} rfl stack
        (held before found (exit.symm.trans live) (parked token waiting) role assigned))
  · have other : id ≠ after.id := by intro equal; exact same (equal.trans key)
    have old : machine.fiber? id = some fiber := by
      rw [RunMachine.fiber?_update_other after machine id other] at selected
      exact selected
    exact frame_machine machine (machine.update after) role _ rfl view
      (held fiber old live waiting role assigned)

/-- Actual interruption retains stored tasks and can only clear an existing park guard. -/
theorem interrupt_metadata (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV) :
    (interruptWithCause cause fiber).1.dispatcher = fiber.dispatcher ∧
    (∀ token, (interruptWithCause cause fiber).1.parked = .withGuard token → fiber.parked = .withGuard token) := by
  unfold interruptWithCause
  split
  · exact ⟨rfl, fun _ same => same⟩
  · dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
    split
    · split
      · exact ⟨rfl, fun _ same => same⟩
      · exact ⟨rfl, fun _ impossible => by cases impossible⟩
    · exact ⟨rfl, fun _ same => same⟩

/-- Every existing reply retains its actual live-token obligation after an addressed interruption. -/
theorem interrupt_reply (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV) (id : FiberId) (token : Nat) (code : NCode)
    (found : machine.fiber? fiber.id = some fiber) (unique : (machine.fibers.map (·.id)).Nodup)
    (held : ReplyAt world machine id token code) :
    ReplyAt world (machine.update (interruptWithCause cause fiber).1) id token code := by
  have fields := HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause
  exact reply_update world machine fiber _ id token code found (StackLedger.interruptWithCause_key cause fiber)
    fields.1 fields.2.2.1 (interrupt_metadata fiber cause).2 (interrupt_view machine fiber cause found unique) held


/-- Detached tasks reuse a producer into the same chosen next proof world. -/
theorem snapshot_replies_into (world next : HostTimeoutNumberConfiguration.World)
    (before after : Effect4.Program.NativeMachine) (tasks : List NTask)
    (replies : ∀ id token code, ReplyAt world before id token code → ReplyAt next after id token code)
    (held : Snapshot world before tasks) : Snapshot next after tasks := by
  intro task member
  have good := held task member
  cases task with
  | resume id token code => exact replies id token code good
  | start id => trivial
  | wake id token => exact good

/-- The existing same-world snapshot interface remains an instance. -/
theorem snapshot_replies (world : HostTimeoutNumberConfiguration.World)
    (before after : Effect4.Program.NativeMachine) (tasks : List NTask)
    (replies : ∀ id token code, ReplyAt world before id token code → ReplyAt world after id token code)
    (held : Snapshot world before tasks) : Snapshot world after tasks :=
  snapshot_replies_into world world before after tasks replies held

/-- The existing actual addressed-row update retains explicit role relabeling in the same joined world. -/
theorem configuration_update_roles (world next : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber) (found : machine.fiber? before.id = some before)
    (key : after.id = before.id) (dispatcher : after.dispatcher = before.dispatcher)
    (view : (machine.update after).completedExits = machine.completedExits)
    (held : Configuration world machine)
    (phase : next.phase = world.phase)
    (unique : ∀ id first second, (id, first) ∈ next.roles → (id, second) ∈ next.roles → first = second)
    (replacement : ∀ role, (before.id, role) ∈ world.roles →
      ∃ selected, (after.id, selected) ∈ next.roles ∧ FiberAt machine selected after)
    (retained : ∀ fiber ∈ machine.fibers, fiber.id ≠ after.id → ∀ role,
      (fiber.id, role) ∈ world.roles → FiberAt machine role fiber →
      ∃ selected, (fiber.id, selected) ∈ next.roles ∧ FiberAt machine selected fiber)
    (replies : ∀ id token code, ReplyAt world machine id token code →
      ReplyAt next (machine.update after) id token code)
    (phases : ∀ id context, (id, Role.pending context) ∈ next.roles → PendingPhase context next.phase) : Configuration next (machine.update after) := by
  constructor
  · rw [phase]; exact held.heap
  · intro fiber member
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal]
    change ∃ role, ((if old.id = after.id then after else old).id, role) ∈ next.roles ∧
      FiberAt (machine.update after) role (if old.id = after.id then after else old)
    split
    · rename_i same
      obtain ⟨role, assigned, good⟩ := held.roles old present
      have oldKey : old.id = before.id := same.trans key
      rw [oldKey] at assigned
      obtain ⟨selected, assigned, good⟩ := replacement role assigned
      exact ⟨selected, assigned, fiber_machine machine (machine.update after) selected after rfl view good⟩
    · rename_i different
      obtain ⟨role, assigned, good⟩ := held.roles old present
      obtain ⟨selected, assigned, good⟩ := retained old present different role assigned good
      exact ⟨selected, assigned, fiber_machine machine (machine.update after) selected old rfl view good⟩
  · exact unique
  · intro fiber member bucket stored
    obtain ⟨old, present, equal⟩ := List.mem_map.mp member
    rw [← equal] at stored
    change bucket ∈ (if old.id = after.id then after else old).dispatcher.buckets at stored
    split at stored
    · rw [dispatcher] at stored
      exact snapshot_replies_into world next machine (machine.update after) bucket.tasks replies
        (held.dispatchers before (RunMachine.mem_of_fiber? found) bucket stored)
    · exact snapshot_replies_into world next machine (machine.update after) bucket.tasks replies
        (held.dispatchers old present bucket stored)

  · exact phases

/-- The original same-role update is an instance of the joined role producer. -/
theorem configuration_update (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber) (found : machine.fiber? before.id = some before)
    (key : after.id = before.id) (dispatcher : after.dispatcher = before.dispatcher)
    (view : (machine.update after).completedExits = machine.completedExits)
    (held : Configuration world machine)
    (replacement : ∀ role, (before.id, role) ∈ world.roles → FiberAt machine role after)
    (replies : ∀ id token code, ReplyAt world machine id token code →
      ReplyAt world (machine.update after) id token code) : Configuration world (machine.update after) := by
  apply configuration_update_roles world world machine before after found key dispatcher view held rfl held.unique
  · intro role assigned
    exact ⟨role, key ▸ assigned, replacement role assigned⟩
  · intro fiber member different role assigned good
    exact ⟨role, assigned, good⟩
  · exact replies
  · exact held.pendingPhase

/-- Actual addressed interruption retains the whole numeric machine assertion and every stored reply obligation. -/
theorem interrupt_configuration (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (found : machine.fiber? fiber.id = some fiber) (unique : (machine.fibers.map (·.id)).Nodup)
    (held : Configuration world machine) (incoming : HostTimeoutNumberFlow.NoTypedFailure cause) :
    Configuration world (machine.update (interruptWithCause cause fiber).1) := by
  apply configuration_update world machine fiber _ found (StackLedger.interruptWithCause_key cause fiber)
    (interrupt_metadata fiber cause).1 (interrupt_view machine fiber cause found unique) held
  · intro role assigned
    exact HostTimeoutNumberConfigurationInterrupt.interrupt_fiber machine role fiber cause
      (held.lookup world machine fiber.id role assigned fiber found) incoming
  · intro id token code good
    exact interrupt_reply world machine fiber cause id token code found unique good

end Test.Dogfood.Proofs.HostTimeoutNumberConfigurationTransport
