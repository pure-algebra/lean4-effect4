import Test.Dogfood.Proofs.HostTimeoutNumberConfigurationTransport

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: actual addressed interruption retains pending numeric replies and cleanup barriers.
Consumer: the contextual admitted-message producer of both Timeout numeric goals.
Reach: actual lookup, matching token, unique fiber ids, and protected pending loop commands.
Limit: the native producer must certify its actual message word and protected owner list.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberQueueInterrupt
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutState HostTimeoutNumberConfiguration HostTimeoutNumberConfigurationTransport

/-- The actual replacement lookup retains every target and the exit used by cancellation waits. -/
theorem update_lookup_exit (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber)
    (found : machine.fiber? before.id = some before) (key : after.id = before.id)
    (exit : after.exit = before.exit) (id : FiberId) :
    ((∃ fiber, machine.fiber? id = some fiber) → ∃ fiber, (machine.update after).fiber? id = some fiber) ∧
    (∀ fiber, (machine.update after).fiber? id = some fiber →
      ∃ old, machine.fiber? id = some old ∧ fiber.exit = old.exit) := by
  by_cases same : id = before.id
  · subst id
    have self : (machine.update after).fiber? before.id = some after := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
    constructor
    · intro existsOld
      exact ⟨after, self⟩
    · intro fiber actual
      rw [self] at actual
      cases actual
      exact ⟨before, found, exit⟩
  · have other : id ≠ after.id := by intro equal; exact same (equal.trans key)
    have lookup := RunMachine.fiber?_update_other after machine id other
    constructor
    · intro existsOld
      rw [lookup]
      exact existsOld
    · intro fiber actual
      exact ⟨fiber, lookup ▸ actual, rfl⟩

/-- Actual cancellation barriers depend only on retained target exits and the unchanged numeric heap. -/
theorem cleanup_await_update (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber) (targets : List FiberId)
    (found : machine.fiber? before.id = some before) (key : after.id = before.id)
    (exit : after.exit = before.exit) (held : CleanupAwait machine targets) :
    CleanupAwait (machine.update after) targets := by
  rcases held with ready | ⟨attempt, member, present, complete⟩
  · exact Or.inl ready
  · refine Or.inr ⟨attempt, member, (update_lookup_exit machine before after found key exit attempt).1 present, ?_⟩
    intro fiber actual published
    obtain ⟨old, previous, same⟩ := (update_lookup_exit machine before after found key exit attempt).2 fiber actual
    exact complete old previous (same ▸ published)

/-- The earlier cleanup image barrier uses the same actual exit transport. -/
theorem await_update (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber) (targets : List FiberId)
    (image : HostTimeoutNumberFlow.Image) (own : image.count = image.cleanups.length + 1)
    (found : machine.fiber? before.id = some before) (key : after.id = before.id)
    (exit : after.exit = before.exit) (held : HostTimeoutNumberWait.AwaitAt image own machine targets) :
    HostTimeoutNumberWait.AwaitAt image own (machine.update after) targets := by
  rcases held with ready | ⟨attempt, member, present, complete⟩
  · exact Or.inl ready
  · refine Or.inr ⟨attempt, member,
      (update_lookup_exit machine before after found key exit attempt).1 present, ?_⟩
    intro fiber actual published
    obtain ⟨old, previous, same⟩ := (update_lookup_exit machine before after found key exit attempt).2 fiber actual
    exact complete old previous (same ▸ published)

/-- An actual admitted interrupt leaves an existing queued pending-prefix loop permission valid. -/
theorem loop_interrupt (context : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV) (id : FiberId) (yielding : Bool)
    (found : machine.fiber? fiber.id = some fiber)
    (coverage : Protects context world machine commands)
    (allowed : MessageAllowed context (.interrupt fiber.id cause))
    (queued : .loop id yielding ∈ commands) (held : CommandAt world machine (.loop id yielding)) :
    CommandAt world (machine.update (interruptWithCause cause fiber).1) (.loop id yielding) := by
  intro count assigned heap after actual installed
  have fields := HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause
  have key := StackLedger.interruptWithCause_key cause fiber
  by_cases same : id = fiber.id
  · subst id
    have self : (machine.update (interruptWithCause cause fiber).1).fiber? fiber.id =
        some (interruptWithCause cause fiber).1 := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨fiber, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at actual
    cases actual
    have oldInstalled : CountInstalled count fiber.frame := by
      change _ ∈ fiber.frame.stack
      change _ ∈ (interruptWithCause cause fiber).1.frame.stack at installed
      rw [fields.2.2.1] at installed
      exact installed
    exact False.elim (allowed.2.2 (coverage fiber.id count yielding fiber assigned heap found oldInstalled queued))
  · have other : id ≠ (interruptWithCause cause fiber).1.id := by
      intro equal
      exact same (equal.trans key)
    have old : machine.fiber? id = some after := by
      rw [RunMachine.fiber?_update_other _ machine id other] at actual
      exact actual
    exact held count assigned heap after old installed


/-- The actual admitted interrupt transports each existing queued numeric command. -/
theorem command_interrupt (context : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV) (command : Guard.NCmd)
    (found : machine.fiber? fiber.id = some fiber) (unique : (machine.fibers.map (·.id)).Nodup)
    (coverage : Protects context world machine commands)
    (allowed : MessageAllowed context (.interrupt fiber.id cause))
    (queued : command ∈ commands) (held : CommandAt world machine command) :
    CommandAt world (machine.update (interruptWithCause cause fiber).1) command := by
  have key := StackLedger.interruptWithCause_key cause fiber
  have exit := (HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause).1
  cases command with
  | resume id token code => exact interrupt_reply world machine fiber cause id token code found unique held
  | loop id yielding => exact loop_interrupt context world machine commands fiber cause id yielding found coverage allowed queued held
  | finish id selected =>
      intro role assigned
      exact exit_machine machine _ role selected rfl (interrupt_view machine fiber cause found unique) (held role assigned)
  | afterInterrupt host yielding kind =>
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll targets =>
          constructor
          · intro image own suffix assigned
            exact await_update machine fiber _ targets image own found key exit (held.1 image own suffix assigned)
          · intro suffix assigned
            exact cleanup_await_update machine fiber _ targets found key exit (held.2 suffix assigned)
  | raceCancel race host yielding remaining visited =>
      constructor
      · intro image own suffix assigned
        exact await_update machine fiber _ (remaining ++ visited) image own found key exit
          (held.1 image own suffix assigned)
      · intro suffix assigned
        exact cleanup_await_update machine fiber _ (remaining ++ visited) found key exit (held.2 suffix assigned)
  | trackChild parent child => exact held
  | closeParAwait host yielding fibers => exact held
  | link mode scope target who extra => exact held
  | wake list phase => exact held
  | evaluate id => trivial
  | deliver id yielding => trivial
  | launch race => trivial
  | enrollRace race child => trivial
  | registrationDone race yielding => trivial
  | interruptTarget target who extra => trivial
  | observe id selected observer => trivial
  | exitDone id => trivial
  | drainDue => trivial

/-- The actual addressed message retains the complete old queue and its generated evaluate suffix. -/
theorem commands_interrupt (context : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (found : machine.fiber? fiber.id = some fiber) (unique : (machine.fibers.map (·.id)).Nodup)
    (coverage : Protects context world machine commands)
    (allowed : MessageAllowed context (.interrupt fiber.id cause)) (held : Commands world machine commands) :
    Commands world (machine.update (interruptWithCause cause fiber).1)
      (commands ++ if (interruptWithCause cause fiber).2 then [.evaluate fiber.id] else []) := by
  intro command member
  rcases List.mem_append.mp member with previous | generated
  · exact command_interrupt context world machine commands fiber cause command found unique coverage allowed previous
      (held command previous)
  · cases evaluate : (interruptWithCause cause fiber).2 with
    | false => simp only [evaluate, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at generated
    | true =>
        simp only [evaluate, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at generated
        rw [generated]
        trivial


/-- The protected owner list remains valid for the retained queue and actual generated evaluate command. -/
theorem protects_interrupt (context : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (found : machine.fiber? fiber.id = some fiber) (coverage : Protects context world machine commands) :
    Protects context world (machine.update (interruptWithCause cause fiber).1)
      (commands ++ if (interruptWithCause cause fiber).2 then [.evaluate fiber.id] else []) := by
  intro id count yielding after assigned heap actual installed queued
  have previous : .loop id yielding ∈ commands := by
    rcases List.mem_append.mp queued with previous | generated
    · exact previous
    · cases evaluate : (interruptWithCause cause fiber).2 with
      | false => simp only [evaluate, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at generated
      | true =>
          simp only [evaluate, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at generated
          cases generated
  have key := StackLedger.interruptWithCause_key cause fiber
  by_cases same : id = fiber.id
  · subst id
    have self : (machine.update (interruptWithCause cause fiber).1).fiber? fiber.id =
        some (interruptWithCause cause fiber).1 := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨fiber, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at actual
    cases actual
    apply coverage fiber.id count yielding fiber assigned heap found _ previous
    change _ ∈ fiber.frame.stack
    change _ ∈ (interruptWithCause cause fiber).1.frame.stack at installed
    rw [(HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause).2.2.1] at installed
    exact installed
  · have other : id ≠ (interruptWithCause cause fiber).1.id := by
      intro equal
      exact same (equal.trans key)
    have old : machine.fiber? id = some after := by
      rw [RunMachine.fiber?_update_other _ machine id other] at actual
      exact actual
    exact coverage id count yielding after assigned heap old installed previous

/-- The actual admitted interrupt retains machine, pending queue, detached tasks, and prefix protection together. -/
theorem interrupt_joint (context : MessageContext) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd) (tasks : List NTask)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (cause : CauseV)
    (found : machine.fiber? fiber.id = some fiber) (unique : (machine.fibers.map (·.id)).Nodup)
    (held : Configuration world machine) (queued : Commands world machine commands)
    (detached : Snapshot world machine tasks) (coverage : Protects context world machine commands)
    (allowed : MessageAllowed context (.interrupt fiber.id cause)) :
    let next := machine.update (interruptWithCause cause fiber).1
    let pending := commands ++ if (interruptWithCause cause fiber).2 then [.evaluate fiber.id] else []
    Configuration world next ∧ Commands world next pending ∧ Snapshot world next tasks ∧
      Protects context world next pending := by
  exact ⟨interrupt_configuration world machine fiber cause found unique held allowed.1,
    commands_interrupt context world machine commands fiber cause found unique coverage allowed queued,
    snapshot_replies world machine _ tasks
      (fun id token code good => interrupt_reply world machine fiber cause id token code found unique good) detached,
    protects_interrupt context world machine commands fiber cause found coverage⟩

end Test.Dogfood.Proofs.HostTimeoutNumberQueueInterrupt
