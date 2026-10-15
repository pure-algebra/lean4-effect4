import Test.Dogfood.Proofs.HostTimeoutNumberPendingInstall

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the actual cleanup write closes the counted attempt while retaining the joined numeric state and queue.
Consumer: the cleanup source branch of the coupled Timeout history producer for both numeric endpoints.
Reach: one actual counted attempt, passive siblings, its actual masked cleanup writer, and the saved numeric restore path.
Limit: the source and runtime authority remain explicit inputs until the full command producer supplies them.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberCleanupJoint
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutState HostTimeoutFlow HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow
open HostTimeoutNumberConfigurationTransport HostTimeoutNumberPassive HostTimeoutNumberCountMachine
open HostTimeoutNumberQueueInterrupt HostTimeoutNumberCallbacks

/-- The pending context owns exactly the cleanup gap created by its counter write. -/
theorem own (context : CountContext) : context.entered.count = context.entered.cleanups.length + 1 := by
  change context.before.count + 1 = context.before.cleanups.length + 1
  rw [context.cleanups]

/-- Cleanup commits the actual interruption bit while retaining the counted attempt number. -/
def cleaned (context : CountContext) (selected : ExitV) :=
  context.entered.cleanup (own context) (HostTimeoutNumberSteps.interruptionFlag selected)

/-- The cleanup heap still differs from the pending attempt's predecessor count. -/
theorem before_ne (context : CountContext) (selected : ExitV) : (cleaned context selected).heap ≠ context.before.heap := by
  intro equal
  have cell := congrArg (fun (heap : RefHeap) => heap[0]?) equal
  change some (Val.nat (context.before.count + 1)) = some (.nat context.before.count) at cell
  have number := congrArg (fun value : Val => match value with | .nat n => n | _ => 0) (Option.some.inj cell)
  change context.before.count + 1 = context.before.count at number
  omega

/-- An actual masked cleanup write retains every pending-fiber field in the committed store. -/
theorem fiber (context : CountContext) (machine : NativeMachine) (row : SourceScope.SourceFiber)
    (selected : ExitV) (held : FiberAt machine (.pending context) row) (live : row.exit = none)
    (heap : At context.entered machine.state) (masked : row.frame.interruptible = false)
    (saved : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state)
      (.unit (cleaned context selected)) (.attempt context.before context.entered (own context)) row.frame.stack) :
    let state := {machine.state with refs := (cleaned context selected).heap}
    let after := {row with frame := {row.frame with current := .success .unit}}
    FiberAt (installed machine state after) (.pending context) after := by
  have future : HostTimeoutNumberFlow.Future machine.state {machine.state with refs := (cleaned context selected).heap} := by
    constructor
    · change machine.state.refs.length ≤ 3
      rw [heap]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  constructor
  · constructor
    · exact ⟨⟨trivial, held.frame.1.saved⟩, trivial, held.frame.1.savedWrites⟩
    · refine ⟨.unit (cleaned context selected), CodeAt.success _ .unit ⟨rfl, rfl⟩, ?_⟩
      exact Effect4.Contracts.Path.map (fun input output code edge =>
        HostTimeoutNumberUniform.Edge.future _ _ input output code future edge) saved
  · intro exit returned
    rw [live] at returned
    cases returned
  · intro impossible; cases impossible
  · exact held.recorded
  · intro cause clean alive idle interruptible
    change row.frame.interruptible = true at interruptible
    rw [masked] at interruptible
    cases interruptible
  · intro next same oldHeap installedFin
    cases same
    exact False.elim (before_ne context selected oldHeap)

  · intro next same entered interruptible
    cases same
    have ready : CleanupReady (installed machine {machine.state with refs := (cleaned context selected).heap}
        {row with frame := {row.frame with current := .success .unit}}).state := by
      refine ⟨cleaned context selected, rfl, ?_⟩
      change (context.entered.cleanups ++ _).length = context.entered.count
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      exact (own context).symm
    have equal := cleanup_ready_phase context.entered _ entered ready
    have impossible := own context
    have contradiction : False := by omega
    exact False.elim contradiction

/-- The actual cleanup writer returns one joined machine, old queue, and detached snapshot at its committed phase. -/
theorem joint (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (machine : NativeMachine) (row : SourceScope.SourceFiber) (selected : ExitV)
    (pending : List Guard.NCmd) (tasks : List NTask)
    (census : OnlyAttempt world row.id context) (found : machine.fiber? row.id = some row)
    (assigned : (row.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (live : row.exit = none)
    (unparked : row.parked = .notParked) (masked : row.frame.interruptible = false)
    (heap : At context.entered machine.state) (nonempty : row.frame.stack ≠ [])
    (saved : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state)
      (.unit (cleaned context selected)) (.attempt context.before context.entered (own context)) row.frame.stack) :
    let state := {machine.state with refs := (cleaned context selected).heap}
    let after := {row with frame := {row.frame with current := .success .unit}}
    let next := installed machine state after
    Configuration {world with phase := cleaned context selected} next ∧
      Commands {world with phase := cleaned context selected} next pending ∧
      Snapshot {world with phase := cleaned context selected} next tasks := by
  let state := {machine.state with refs := (cleaned context selected).heap}
  let after : SourceScope.SourceFiber := {row with frame := {row.frame with current := .success .unit}}
  let next := installed machine state after
  have replies : ∀ id token code, ReplyAt world machine id token code → ReplyAt world next id token code :=
    fun id token code good => reply_store world machine context row after state census found rfl unparked id token code good
  have config := configuration_store world machine context row after state (cleaned context selected) census found assigned
    rfl unparked rfl rfl held (fiber context machine row selected (held.lookup world machine row.id (.pending context) assigned row found)
      live heap masked saved)
  have queue : Commands world next pending := by
    intro command member
    apply command_transport world machine next pending command member (queued command member) replies
    · intro id yielding member previous nextContext roleAt oldHeap other actual installedFin
      rcases census id (.pending nextContext) roleAt with ⟨same, equal⟩ | passive
      · cases equal
        exact False.elim (before_ne context selected oldHeap)
      · cases passive
    · intro id exit previous
      by_cases same : id = row.id
      · subst id
        exact False.elim (nonempty (previous.1 row found))
      · exact ⟨terminal_update {machine with state} row after id found rfl rfl previous.1,
          fun role roleAt => exit_store next role exit (other_passive world row.id context id role census roleAt same)⟩
    · intro host yielding kind member previous
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll targets =>
        exact ⟨fun image own suffix roleAt => False.elim
          (HostTimeoutNumberCountQueue.no_legacy world context row.id host image own suffix census roleAt),
          fun suffix roleAt => Or.inl ⟨cleaned context selected, rfl, by
            change (context.entered.cleanups ++ _).length = context.entered.count
            simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
            exact (own context).symm⟩⟩
    · intro race host yielding remaining visited member previous
      exact ⟨fun image own suffix roleAt => False.elim
        (HostTimeoutNumberCountQueue.no_legacy world context row.id host image own suffix census roleAt),
        fun suffix roleAt => Or.inl ⟨cleaned context selected, rfl, by
          change (context.entered.cleanups ++ _).length = context.entered.count
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
          exact (own context).symm⟩⟩
  exact ⟨config, queue, snapshot_replies world machine next tasks replies detached⟩

/-- The real native cleanup dispatch consumes the existing evaluator equation and the joined postcondition. -/
theorem native_joint (world : HostTimeoutNumberConfiguration.World) (context : CountContext)
    (view : HostTimeoutFlow.View) (machine : NativeMachine) (row : SourceScope.SourceFiber)
    (yielding : Bool) (selected : ExitV) (pending : List Guard.NCmd) (tasks : List NTask)
    (census : OnlyAttempt world row.id context) (found : machine.fiber? row.id = some row)
    (assigned : (row.id, Role.pending context) ∈ world.roles)
    (held : Configuration world machine) (queued : Commands world machine pending)
    (detached : Snapshot world machine tasks) (live : row.exit = none)
    (unparked : row.parked = .notParked) (masked : row.frame.interruptible = false)
    (heap : At context.entered machine.state) (nonempty : row.frame.stack ≠ [])
    (saved : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state)
      (.unit (cleaned context selected)) (.attempt context.before context.entered (own context)) row.frame.stack)
    (current : row.frame.current = resolve HostTimeoutSource.program
      (({cleanupPoint context.captured context.fuel context.delay context.n context.previous selected with completed := view}.childWith 1
        (.nat context.entered.count)).child 0)) :
    let next := evaluateNative HostTimeoutSource.program machine row yielding Test.Dogfood.Scenario.Timeout.fetch.table
    Configuration {world with phase := cleaned context selected} (next.machine.update next.fiber) ∧
      Commands {world with phase := cleaned context selected} (next.machine.update next.fiber) pending ∧
      Snapshot {world with phase := cleaned context selected} (next.machine.update next.fiber) tasks ∧
      next.nested = [.drainDue] ∧ next.edits = [] ∧ next.outcome = .answered := by
  have actual := native_cleanup view machine row yielding context.entered (own context) context.captured
    context.fuel context.delay context.n context.previous selected heap _ current
    (HostTimeoutNumberUniform.path view machine.state _ _ row.frame.stack saved)
  dsimp only
  rw [actual.1]
  obtain ⟨config, queue, snapshot⟩ := joint world context machine row selected pending tasks census found assigned
    held queued detached live unparked masked heap nonempty saved
  exact ⟨config, queue, snapshot, rfl, rfl, rfl⟩

end Test.Dogfood.Proofs.HostTimeoutNumberCleanupJoint
