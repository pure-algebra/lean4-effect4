import Test.Dogfood.Proofs.HostTimeoutNumberTerminalFiber

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R9.
Consumer: the finished pending-attempt branch of the actual coupled numeric command producer.
Actual completion supplies cleanup readiness before the numeric role becomes passive.
The existing timer role denotes passive code with no numeric writer, including completed actors.
Reach: the same actual heap, unique stored owner, drained returned frame, and admitted queued replies.
This role update proves no progress or application history by itself.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberRetirement
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow HostTimeoutState
open HostTimeoutNumberConfigurationTransport

/-- The completed actor keeps its existing identity and receives the existing passive role. -/
def passive (world : HostTimeoutNumberConfiguration.World) (target : FiberId) : HostTimeoutNumberConfiguration.World :=
  {world with roles := world.roles.map fun pair =>
    (pair.1, if pair.1 = target then Role.timer else pair.2)}

/-- Role membership retains the actual old assignment and its deterministic relabeling. -/
theorem passive_member (world : HostTimeoutNumberConfiguration.World) (target id : FiberId) (role : Role) :
    (id, role) ∈ (passive world target).roles ↔
      ∃ old, (id, old) ∈ world.roles ∧ role = (if id = target then Role.timer else old) := by
  constructor
  · intro member
    obtain ⟨⟨key, old⟩, present, equal⟩ := List.mem_map.mp member
    have keys := congrArg Prod.fst equal
    dsimp only at keys
    subst key
    exact ⟨old, present, (congrArg Prod.snd equal).symm⟩
  · rintro ⟨old, present, rfl⟩
    exact List.mem_map.mpr ⟨(id, old), present, rfl⟩

/-- The same actual unique role table remains unique after the completed owner becomes passive. -/
theorem passive_unique (world : HostTimeoutNumberConfiguration.World) (target : FiberId)
    (unique : ∀ id first second, (id, first) ∈ world.roles → (id, second) ∈ world.roles → first = second) :
    ∀ id first second, (id, first) ∈ (passive world target).roles →
      (id, second) ∈ (passive world target).roles → first = second := by
  intro id first second before after
  obtain ⟨oldFirst, oldBefore, rfl⟩ := (passive_member world target id first).mp before
  obtain ⟨oldSecond, oldAfter, rfl⟩ := (passive_member world target id second).mp after
  rw [unique id oldFirst oldSecond oldBefore oldAfter]

/-- Other actual owners retain their original role after the completed actor becomes passive. -/
theorem passive_other (world : HostTimeoutNumberConfiguration.World) (target id : FiberId) (role : Role)
    (different : id ≠ target) :
    (id, role) ∈ (passive world target).roles ↔ (id, role) ∈ world.roles := by
  constructor
  · intro member
    obtain ⟨old, present, equal⟩ := (passive_member world target id role).mp member
    rw [if_neg different] at equal
    exact equal.symm ▸ present
  · intro member
    exact (passive_member world target id role).mpr ⟨role, member, (if_neg different).symm⟩

/-- Existing replies remain stale for the actual unparked completed actor and retain every other role's permission. -/
theorem passive_reply (world : HostTimeoutNumberConfiguration.World) (machine : NativeMachine)
    (before after : SourceScope.SourceFiber) (found : machine.fiber? before.id = some before)
    (key : after.id = before.id) (unparked : after.parked = .notParked)
    (view : (machine.update after).completedExits = machine.completedExits)
    (id : FiberId) (token : Nat) (code : NCode) (held : ReplyAt world machine id token code) :
    ReplyAt (passive world before.id) (machine.update after) id token code := by
  have old := HostTimeoutNumberPendingInstall.replies world machine before after found key unparked view id token code held
  intro fiber selected live parked role assigned
  by_cases same : id = before.id
  · subst id
    have self : (machine.update after).fiber? before.id = some after := by
      rw [← key]
      exact RunMachine.fiber?_update_self after machine ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at selected
    cases selected
    rw [unparked] at parked
    cases parked
  · exact old fiber selected live parked role ((passive_other world before.id id role same).mp assigned)

/-- A nonpassive new assignment retains its actual distinct original owner and role. -/
theorem passive_active (world : HostTimeoutNumberConfiguration.World) (target id : FiberId) (role : Role)
    (assigned : (id, role) ∈ (passive world target).roles) (active : role ≠ .timer) :
    id ≠ target ∧ (id, role) ∈ world.roles := by
  obtain ⟨old, present, same⟩ := (passive_member world target id role).mp assigned
  by_cases equal : id = target
  · rw [if_pos equal] at same
    exact (active same).elim
  · rw [if_neg equal] at same
    exact ⟨equal, same.symm ▸ present⟩

/-- The actual completed actor becomes passive only after cleanup readiness, retaining the whole joined assertion. -/
theorem passive_update (world : HostTimeoutNumberConfiguration.World) (machine : NativeMachine)
    (before after : SourceScope.SourceFiber) (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? before.id = some before) (key : after.id = before.id)
    (dispatcher : after.dispatcher = before.dispatcher) (exitSame : after.exit = before.exit)
    (unparked : after.parked = .notParked) (empty : after.frame.stack = [])
    (view : (machine.update after).completedExits = machine.completedExits)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (provided : FiberAt machine .timer after)
    (cleaned : CleanupReady machine.state) :
    Configuration (passive world before.id) (machine.update after) ∧
      Commands (passive world before.id) (machine.update after) pending ∧
      Snapshot (passive world before.id) (machine.update after) tasks := by
  have reply := passive_reply world machine before after found key unparked view
  have config : Configuration (passive world before.id) (machine.update after) := by
    apply configuration_update_roles world (passive world before.id) machine before after found key dispatcher view held
      rfl (passive_unique world before.id held.unique)
    · intro role assigned
      refine ⟨.timer, ?_, provided⟩
      apply (passive_member world before.id after.id .timer).mpr
      refine ⟨role, key.symm ▸ assigned, ?_⟩
      rw [if_pos key]
    · intro fiber member different role assigned good
      have other : fiber.id ≠ before.id := fun same => different (same.trans key.symm)
      exact ⟨role, (passive_other world before.id fiber.id role other).mpr assigned, good⟩
    · exact reply
    · intro id context assigned
      obtain ⟨different, old⟩ := passive_active world before.id id (.pending context) assigned (by intro equal; cases equal)
      exact held.pendingPhase id context old
  have queue : Commands (passive world before.id) (machine.update after) pending := by
    intro command member
    apply HostTimeoutNumberQueueInterrupt.command_transport_into world (passive world before.id)
      machine _ pending command member (queued command member) reply
    · intro id yielding present previous context assigned heap fiber selected installed
      obtain ⟨different, old⟩ := passive_active world before.id id (.pending context) assigned (by intro equal; cases equal)
      have other : id ≠ after.id := fun same => different (same.trans key)
      rw [RunMachine.fiber?_update_other after machine id other] at selected
      exact previous context old heap fiber selected installed
    · intro id selected present previous
      constructor
      · intro fiber actual
        by_cases same : id = before.id
        · subst id
          have self : (machine.update after).fiber? before.id = some after := by
            rw [← key]
            exact RunMachine.fiber?_update_self after machine ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
          rw [self] at actual
          cases actual
          exact empty
        · have other : id ≠ after.id := fun equal => same (equal.trans key)
          rw [RunMachine.fiber?_update_other after machine id other] at actual
          exact previous.1 fiber actual
      · intro role assigned
        by_cases same : id = before.id
        · obtain ⟨old, original, equal⟩ := (passive_member world before.id id role).mp assigned
          rw [if_pos same] at equal
          rw [equal]
          trivial
        · exact exit_machine machine _ role selected rfl view
            (previous.2 role ((passive_other world before.id id role same).mp assigned))
    · intro host yielding kind present previous
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll targets =>
        constructor
        · intro image own suffix assigned
          obtain ⟨different, old⟩ := passive_active world before.id host (.root image own suffix) assigned (by intro equal; cases equal)
          exact HostTimeoutNumberQueueInterrupt.await_update machine before after targets image own found key exitSame
            (previous.1 image own suffix old)
        · intro suffix assigned
          exact Or.inl cleaned
    · intro race host yielding remaining visited present previous
      constructor
      · intro image own suffix assigned
        obtain ⟨different, old⟩ := passive_active world before.id host (.root image own suffix) assigned (by intro equal; cases equal)
        exact HostTimeoutNumberQueueInterrupt.await_update machine before after (remaining ++ visited) image own found key exitSame
          (previous.1 image own suffix old)
      · intro suffix assigned
        exact Or.inl cleaned
  exact ⟨config, queue, snapshot_replies_into world (passive world before.id) machine _ tasks reply detached⟩

/-- Actual attempt completion supplies cleanup readiness before the returned actor becomes passive. -/
theorem finished_handoff (context : CountContext) (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (selected exit : ExitV)
    (held : FiberAt machine (.pending context) fiber)
    (current : fiber.frame.current = Prim.ofExit selected) (clear : fiber.frame.deferredInterrupt = false)
    (finished : (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding selected).outcome = .finished exit) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding selected
    FiberAt next.machine .timer next.fiber ∧ CleanupReady machine.state := by
  have cleaned := HostTimeoutNumberTerminal.finished_actual context view machine fiber yielding selected exit held current clear finished
  have passiveNative :
      let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding selected
      next.outcome = .finished exit → FiberAt next.machine .timer next.fiber := by
    apply AnswerFlow.External.Native.finalizer_dispatch (HostTimeoutFlow.interpreter view) machine fiber yielding selected
      (fun result => result.outcome = .finished exit → FiberAt result.machine .timer result.fiber)
    · intro absent stopped
      cases actual : fiber.frame.step (HostTimeoutFlow.interpreter view).toPrimInterp with
      | mk step events =>
        cases step with
        | running frame =>
          simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame] at stopped
          cases stopped
        | finished returned =>
          exact HostTimeoutNumberTerminal.finished_native view machine fiber yielding returned ⟨selected, current⟩
            held.recorded (congrArg Prod.fst actual)
    · intro body name flag program chosen installed stopped
      obtain ⟨rows, completed, key, dispatcher, parked, nested, edits, outcome, deferred⟩ :=
        HostTimeoutNumberProtected.installed_metadata_deferred view machine fiber yielding selected body name flag program chosen installed
      rw [outcome] at stopped
      cases stopped
  exact ⟨passiveNative finished, cleaned⟩

/-- The finished native attempt installs its actual passive row in one joined next numeric world. -/
theorem joint_finished (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (resident charged : SourceScope.SourceFiber) (yielding : Bool) (selected exit : ExitV)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? resident.id = some resident) (ids : (machine.fibers.map (·.id)).Nodup)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (provided : FiberAt machine (.pending context) charged)
    (key : charged.id = resident.id) (dispatcher : charged.dispatcher = resident.dispatcher)
    (exitSame : charged.exit = resident.exit) (unparked : charged.parked = .notParked)
    (current : charged.frame.current = Prim.ofExit selected) (clear : charged.frame.deferredInterrupt = false)
    (finished : (evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding selected).outcome = .finished exit) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding selected
    Configuration (passive world resident.id) (next.machine.update next.fiber) ∧
      Commands (passive world resident.id) (next.machine.update next.fiber) pending ∧
      Snapshot (passive world resident.id) (next.machine.update next.fiber) tasks ∧
      next.nested = [] ∧ next.edits = [] ∧ next.outcome = .finished exit := by
  obtain ⟨retained, cleaned⟩ := finished_handoff context view machine charged yielding selected exit provided current clear finished
  have empty := (Effect4.Machine.finalizerOr_keepsMask (HostTimeoutFlow.interpreter view) machine charged yielding selected).finished_stack finished
  obtain ⟨events, frame, outcome, actual⟩ := NativeFrameRows.finalizer_frame_only
    (HostTimeoutFlow.interpreter view) machine charged yielding selected
  rw [actual] at retained empty finished ⊢
  have base := configuration_fields world machine (machine.emit events) rfl rfl rfl held
  have baseQueue := HostTimeoutNumberQueueInterrupt.commands_fields world machine (machine.emit events) pending rfl rfl rfl queued
  have baseTasks := snapshot_fields world machine (machine.emit events) tasks rfl rfl rfl detached
  have viewSame := update_view (machine.emit events) resident {charged with frame := frame} found ids key exitSame
  obtain ⟨config, queue, snapshot⟩ := passive_update world (machine.emit events) resident {charged with frame := frame}
    pending tasks found key dispatcher exitSame unparked empty viewSame base baseQueue baseTasks retained cleaned
  exact ⟨config, queue, snapshot, rfl, rfl, finished⟩

/-- Actual terminal native dispatch either continues with its returned frame or finishes with its delivered exit. -/
theorem terminal_outcomes (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (selected : ExitV) :
    let result := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding selected
    result.outcome = .continue_ ∨ ∃ exit, result.outcome = .finished exit := by
  apply AnswerFlow.External.Native.finalizer_dispatch (HostTimeoutFlow.interpreter view) machine fiber yielding selected
    (fun result => result.outcome = .continue_ ∨ ∃ exit, result.outcome = .finished exit)
  · intro absent
    unfold evaluatePrim.stepFrame
    cases actual : fiber.frame.step (HostTimeoutFlow.interpreter view).toPrimInterp with
    | mk step events =>
      cases step with
      | running frame => exact Or.inl rfl
      | finished exit => exact Or.inr ⟨exit, rfl⟩
  · intro body name flag program chosen installed
    obtain ⟨rows, completed, key, dispatcher, parked, nested, edits, outcome, deferred⟩ :=
      HostTimeoutNumberProtected.installed_metadata_deferred view machine fiber yielding selected body name flag program chosen installed
    exact Or.inl outcome

/-- Retiring the only actual numeric writer leaves every assigned role passive for the next source attempt. -/
theorem passive_census (world : HostTimeoutNumberConfiguration.World) (target : FiberId) (context : CountContext)
    (census : HostTimeoutNumberPassive.OnlyAttempt world target context) :
    ∀ id role, (id, role) ∈ (passive world target).roles → HostTimeoutNumberPassive.Passive role := by
  intro id role assigned
  obtain ⟨old, present, same⟩ := (passive_member world target id role).mp assigned
  by_cases equal : id = target
  · rw [if_pos equal] at same
    cases same
    exact .timer
  · rw [if_neg equal] at same
    cases same
    rcases census id role present with ⟨same, pending⟩ | passive
    · exact (equal same).elim
    · exact passive

/-- One actual terminal native producer returns a single numeric world for the installed machine, queue, and detached tasks. -/
theorem joint_terminal (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (resident charged : SourceScope.SourceFiber) (yielding : Bool) (selected : ExitV)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (found : machine.fiber? resident.id = some resident) (ids : (machine.fibers.map (·.id)).Nodup)
    (assigned : (resident.id, Role.pending context) ∈ world.roles)
    (census : HostTimeoutNumberPassive.OnlyAttempt world resident.id context)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (provided : FiberAt machine (.pending context) charged)
    (sourceMachine : SourceScope.ConfigurationAt HostTimeoutSource.program machine)
    (sourceCharged : SourceScope.FiberAt HostTimeoutSource.program charged)
    (key : charged.id = resident.id) (dispatcher : charged.dispatcher = resident.dispatcher)
    (exitSame : charged.exit = resident.exit) (running : charged.running = true)
    (live : charged.exit = none) (unparked : charged.parked = .notParked)
    (finishes : ∀ exit, .finish resident.id exit ∉ pending)
    (loopEntered : ∀ latch, .loop resident.id latch ∈ pending → At context.entered machine.state)
    (current : charged.frame.current = Prim.ofExit selected) (clear : charged.frame.deferredInterrupt = false) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine charged yielding selected
    ∃ nextWorld, HostTimeoutNumberPassive.OnlyAttempt nextWorld resident.id context ∧ Configuration nextWorld (next.machine.update next.fiber) ∧
      Commands nextWorld (next.machine.update next.fiber) pending ∧
      Snapshot nextWorld (next.machine.update next.fiber) tasks ∧ next.nested = [] ∧ next.edits = [] := by
  rcases terminal_outcomes view machine charged yielding selected with continues | ⟨exit, finished⟩
  · obtain ⟨config, queue, snapshot, nested, edits, outcome⟩ := HostTimeoutNumberTerminalFiber.joint_local
      world context view machine resident charged yielding selected pending tasks found ids assigned held queued detached
      provided sourceMachine sourceCharged key dispatcher exitSame running live unparked finishes loopEntered current clear continues
    exact ⟨world, census, config, queue, snapshot, nested, edits⟩
  · obtain ⟨config, queue, snapshot, nested, edits, outcome⟩ := joint_finished world context view machine
      resident charged yielding selected exit pending tasks found ids held queued detached provided key dispatcher exitSame
      unparked current clear finished
    exact ⟨passive world resident.id, fun id role member => Or.inr (passive_census world resident.id context census id role member),
      config, queue, snapshot, nested, edits⟩

end Test.Dogfood.Proofs.HostTimeoutNumberRetirement
