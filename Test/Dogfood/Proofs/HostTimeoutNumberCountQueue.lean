import Test.Dogfood.Proofs.HostTimeoutNumberCountMachine

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: the actual count write retains its pending numeric queue and detached replies.
Consumer: the count branch of the coupled Timeout native and command producer.
Reach: the actual count stack, one active attempt, and cancellation commands naming that actual attempt.
Limit: the race producer must establish the cancellation-target certificate; this file does not assume arbitrary barrier store closure.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberCountQueue
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutState HostTimeoutNumberConfiguration HostTimeoutNumberConfigurationTransport
open HostTimeoutNumberQueueInterrupt HostTimeoutNumberPassive HostTimeoutNumberCountMachine

/-- The post-count row is the actual native sync answer with its retained saved stack. -/
def postFiber (fiber : Effect4.Program.SourceScope.SourceFiber) : Effect4.Program.SourceScope.SourceFiber :=
  {countOp fiber with frame := {fiber.frame with current := .success .unit}}

/-- The actual count installs its incremented store and answered row together. -/
def postMachine (machine : Effect4.Program.NativeMachine) (context : CountContext)
    (fiber : Effect4.Program.SourceScope.SourceFiber) : Effect4.Program.NativeMachine :=
  installed machine {machine.state with refs := context.entered.heap} (postFiber fiber)

/-- Pending root cancellation commands retain their actual active-attempt target. -/
structure Targets (world : HostTimeoutNumberConfiguration.World) (active : FiberId) (commands : List Guard.NCmd) : Prop where
  after : ∀ host yielding targets, .afterInterrupt host yielding (.awaitAll targets) ∈ commands →
    ∀ suffix, (host, Role.rootRead suffix) ∈ world.roles → active ∈ targets
  race : ∀ race host yielding remaining visited, .raceCancel race host yielding remaining visited ∈ commands →
    ∀ suffix, (host, Role.rootRead suffix) ∈ world.roles → active ∈ remaining ++ visited

/-- No pending numeric count can still read the predecessor heap after this actual increment. -/
theorem loop_post (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (fiber : Effect4.Program.SourceScope.SourceFiber) (id : FiberId) (yielding : Bool)
    (census : OnlyAttempt world fiber.id context) :
    CommandAt world (postMachine machine context fiber) (.loop id yielding) := by
  intro next assigned heap after found installedFin
  rcases census id (.pending next) assigned with ⟨same, equal⟩ | passive
  · cases equal
    exact False.elim (counted_heap_ne context heap)
  · cases passive

/-- The unique-attempt census excludes legacy root-image roles from the actual numeric producer. -/
theorem no_legacy (world : HostTimeoutNumberConfiguration.World) (context : CountContext) (active host : FiberId)
    (image : HostTimeoutNumberFlow.Image) (own : image.count = image.cleanups.length + 1) (suffix : List NCode)
    (census : OnlyAttempt world active context) (assigned : (host, Role.root image own suffix) ∈ world.roles) : False := by
  rcases census host (.root image own suffix) assigned with ⟨same, equal⟩ | passive
  · cases equal
  · cases passive

/-- A pending cancellation that names the actual live attempt retains its cleanup barrier after count. -/
theorem await_post (machine : Effect4.Program.NativeMachine) (context : CountContext)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (targets : List FiberId)
    (found : machine.fiber? fiber.id = some fiber) (live : fiber.exit = none) (member : fiber.id ∈ targets) :
    CleanupAwait (postMachine machine context fiber) targets := by
  have self : (postMachine machine context fiber).fiber? fiber.id = some (postFiber fiber) := by
    apply RunMachine.fiber?_update_self
    exact ⟨fiber, RunMachine.mem_of_fiber? found, rfl⟩
  refine Or.inr ⟨fiber.id, member, ⟨postFiber fiber, self⟩, ?_⟩
  intro after actual published
  rw [self] at actual
  cases actual
  change fiber.exit.isSome = true at published
  rw [live] at published
  cases published

/-- The actual count stack excludes an old finish for that active writer; passive finishes retain their exits. -/
theorem finish_post (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (fiber : Effect4.Program.SourceScope.SourceFiber) (id : FiberId) (exit : ExitV)
    (census : OnlyAttempt world fiber.id context) (found : machine.fiber? fiber.id = some fiber)
    (saved : fiber.frame.stack ≠ []) (held : CommandAt world machine (.finish id exit)) :
    CommandAt world (postMachine machine context fiber) (.finish id exit) := by
  by_cases same : id = fiber.id
  · subst id
    exact False.elim (saved (held.1 fiber found))
  · constructor
    · exact terminal_update {machine with state := {machine.state with refs := context.entered.heap}}
        fiber (postFiber fiber) id found rfl rfl held.1
    · intro role assigned
      exact exit_store _ role exit (other_passive world fiber.id context id role census assigned same)

/-- The actual count write retains every old pending command through the same command-assertion producer. -/
theorem commands_post (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (context : CountContext) (fiber : Effect4.Program.SourceScope.SourceFiber) (pending : List Guard.NCmd)
    (census : OnlyAttempt world fiber.id context) (found : machine.fiber? fiber.id = some fiber)
    (live : fiber.exit = none) (unparked : fiber.parked = .notParked) (saved : fiber.frame.stack ≠ [])
    (targets : Targets world fiber.id pending) (held : Commands world machine pending) :
    Commands world (postMachine machine context fiber) pending := by
  intro command member
  exact command_transport world machine _ pending command member (held command member)
    (reply_store world machine context fiber (postFiber fiber) _ census found rfl unparked)
    (fun id yielding queued good => loop_post world machine context fiber id yielding census)
    (fun id exit member good => finish_post world machine context fiber id exit census found saved good)
    (by
      intro host yielding kind queued good
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll awaiting =>
          exact ⟨fun image own suffix assigned => False.elim (no_legacy world context fiber.id host image own suffix census assigned),
            fun suffix assigned => await_post machine context fiber awaiting found live
              (targets.after host yielding awaiting queued suffix assigned)⟩)
    (by
      intro race host yielding remaining visited queued good
      exact ⟨fun image own suffix assigned => False.elim (no_legacy world context fiber.id host image own suffix census assigned),
        fun suffix assigned => await_post machine context fiber (remaining ++ visited) found live
          (targets.race race host yielding remaining visited queued suffix assigned)⟩)

/-- The same active-attempt census makes old prefix protection vacuous after the count commits. -/
theorem protects_post (messageContext : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (context : CountContext)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (pending : List Guard.NCmd)
    (census : OnlyAttempt world fiber.id context) : Protects messageContext world (postMachine machine context fiber) pending := by
  intro id next yielding after assigned heap found installedFin queued
  rcases census id (.pending next) assigned with ⟨same, equal⟩ | passive
  · cases equal
    exact False.elim (counted_heap_ne context heap)
  · cases passive


/-- The actual count keeps arbitrary certified saved frames and the same joined queue and snapshot. -/
theorem count_joint_over (messageContext : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (context : CountContext)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (pending : List Guard.NCmd) (tasks : List NTask)
    (census : OnlyAttempt world fiber.id context) (found : machine.fiber? fiber.id = some fiber)
    (assigned : (fiber.id, Role.pending context) ∈ world.roles) (held : Configuration world machine)
    (queued : Commands world machine pending) (detached : Snapshot world machine tasks)
    (targets : Targets world fiber.id pending) (live : fiber.exit = none)
    (heap : HostTimeoutNumberPhaseFlow.At context.before machine.state)
    (current : fiber.frame.current = context.write)
    (installedFin : CountInstalled context fiber.frame) (ready : CountReady context fiber yielding)
    (numeric : HostTimeoutNumberUniform.FrameAt {machine.state with refs := context.entered.heap}
      (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) {fiber.frame with current := .success .unit}) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    let state := {machine.state with refs := context.entered.heap}
    let next := postMachine machine context fiber
    iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding =
      ⟨{machine with state}, postFiber fiber, yielding, .answered, [.drainDue], []⟩ ∧
    Configuration {world with phase := context.entered} next ∧
    Commands {world with phase := context.entered} next pending ∧
    Snapshot {world with phase := context.entered} next tasks ∧
    Protects messageContext {world with phase := context.entered} next pending := by
  have old := held.lookup world machine fiber.id (.pending context) assigned fiber found
  have charged : FiberAt machine (.pending context) (countOp fiber) :=
    ⟨old.frame, old.exit, old.retired, old.recorded, old.immediate,
      old.pendingRunning, old.pendingCustody, old.pendingDeferred⟩
  have active := counted_fiber_over machine context (countOp fiber) charged live heap installedFin numeric
  have config := configuration_store world machine context fiber (postFiber fiber)
    {machine.state with refs := context.entered.heap} context.entered census found assigned rfl
    ready.2.2 rfl rfl held active (.inr (.inl rfl))
  have saved : fiber.frame.stack ≠ [] := by
    intro empty
    obtain ⟨point, body, source, member⟩ := installedFin
    rw [empty] at member
    cases member
  have answer := HostTimeoutNumberEntry.count_sync machine.state context.before.count context.delay context.n
    context.previous context.before.cleanups context.before.completed
  change syncOpStep (.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm context.point.env)
    {machine.state with refs := context.before.heap} =
      some ({machine.state with refs := context.entered.heap}, .unit) at answer
  have previous : {machine.state with refs := context.before.heap} = machine.state := by rw [← heap]
  rw [previous] at answer
  have evaluated := ControlSteps.native_sync_op HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    machine (countOp fiber) yielding _ _ .unit current answer
  have committed :
      letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
      iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding =
        ⟨{machine with state := {machine.state with refs := context.entered.heap}}, postFiber fiber,
          yielding, .answered, [.drainDue], []⟩ := by
    rw [count_iteration context machine fiber yielding installedFin ready]
    exact evaluated
  exact ⟨committed, config,
    commands_post world machine context fiber pending census found live ready.2.2 saved targets queued,
    snapshot_replies world machine _ tasks
      (reply_store world machine context fiber (postFiber fiber) _ census found rfl ready.2.2) detached,
    protects_post messageContext world machine context fiber pending census⟩

/-- The actual source count head derives its heap, finalizer, and answer permission from one configuration.
Consumer: the pending native branch advances the joined machine, queue, and snapshot. -/
theorem count_joint_frame (messageContext : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (context : CountContext)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (pending : List Guard.NCmd) (tasks : List NTask)
    (census : OnlyAttempt world fiber.id context) (found : machine.fiber? fiber.id = some fiber)
    (assigned : (fiber.id, Role.pending context) ∈ world.roles) (held : Configuration world machine)
    (queued : Commands world machine pending) (detached : Snapshot world machine tasks)
    (targets : Targets world fiber.id pending) (live : fiber.exit = none)
    (term : Term) (env : List Val)
    (current : fiber.frame.current = .sync (.op (.refUpdate ⟨0⟩ term env)))
    (source : SourceScope.FrameAt HostTimeoutSource.program fiber.frame)
    (admitted : CommandAt world machine (.loop fiber.id yielding)) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    let state := {machine.state with refs := context.entered.heap}
    let next := postMachine machine context fiber
    iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding =
      ⟨{machine with state}, postFiber fiber, yielding, .answered, [.drainDue], []⟩ ∧
    Configuration {world with phase := context.entered} next ∧
    Commands {world with phase := context.entered} next pending ∧
    Snapshot {world with phase := context.entered} next tasks ∧
    Protects messageContext {world with phase := context.entered} next pending := by
  have provided := held.lookup world machine fiber.id (.pending context) assigned fiber found
  obtain ⟨input, authored, heap, early, path, good⟩ :=
    count_permission world context machine fiber term env assigned held provided current
  have installedFin := installed_of_path context machine.state fiber.frame input early path provided.frame.1 source
  have ready := admitted context assigned heap fiber found installedFin
  have future : HostTimeoutNumberFlow.Future machine.state {machine.state with refs := context.entered.heap} := by
    constructor
    · change machine.state.refs.length ≤ context.entered.heap.length
      rw [heap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  have numeric : HostTimeoutNumberUniform.FrameAt {machine.state with refs := context.entered.heap}
      (.attempt context.before context.entered (by
        change context.before.count + 1 = context.before.cleanups.length + 1
        rw [context.cleanups])) {fiber.frame with current := .success .unit} := by
    refine ⟨input, .success input .unit good, ?_⟩
    exact path.map (fun first last frame edge => HostTimeoutNumberUniform.Edge.future _ _ first last frame future edge)
  exact count_joint_over messageContext world machine context fiber yielding pending tasks census found assigned
    held queued detached targets live heap authored installedFin ready numeric

/-- The actual native count returns one joined machine, old queue, detached snapshot, and protected-owner assertion. -/
theorem count_joint (messageContext : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (context : CountContext)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (yielding : Bool) (pending : List Guard.NCmd) (tasks : List NTask)
    (census : OnlyAttempt world fiber.id context) (found : machine.fiber? fiber.id = some fiber)
    (assigned : (fiber.id, Role.pending context) ∈ world.roles) (held : Configuration world machine)
    (queued : Commands world machine pending) (detached : Snapshot world machine tasks)
    (targets : Targets world fiber.id pending) (live : fiber.exit = none)
    (heap : HostTimeoutNumberPhaseFlow.At context.before machine.state)
    (current : fiber.frame.current = context.write)
    (stack : fiber.frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
      .onExit context.bound (.fin context.point) false]) (ready : CountReady context fiber yielding) :
    letI := evaluatorFor HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    let state := {machine.state with refs := context.entered.heap}
    let next := postMachine machine context fiber
    iteration (interpOf HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table) machine fiber yielding =
      ⟨{machine with state}, postFiber fiber, yielding, .answered, [.drainDue], []⟩ ∧
    Configuration {world with phase := context.entered} next ∧
    Commands {world with phase := context.entered} next pending ∧
    Snapshot {world with phase := context.entered} next tasks ∧
    Protects messageContext {world with phase := context.entered} next pending := by
  have installedFin : CountInstalled context fiber.frame := by
    apply CountInstalled.exact
    change _ ∈ fiber.frame.stack
    rw [stack]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  exact count_joint_over messageContext world machine context fiber yielding pending tasks census found assigned
    held queued detached targets live heap current installedFin ready
    (counted_frame_uniform context _ fiber.frame rfl stack)

end Test.Dogfood.Proofs.HostTimeoutNumberCountQueue
