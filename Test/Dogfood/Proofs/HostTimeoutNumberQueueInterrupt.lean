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

/-- An actual writer retaining any saved frame cannot have a pending finish command. -/
theorem finish_excludes_saved (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (selected : ExitV)
    (found : machine.fiber? fiber.id = some fiber) (saved : fiber.frame.stack ≠ [])
    (held : Commands world machine commands) : .finish fiber.id selected ∉ commands := by
  intro member
  exact saved ((held (.finish fiber.id selected) member).1 fiber found)

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
      obtain ⟨point, body, source, member⟩ := installed
      exact ⟨point, body, source, fields.2.2.1 ▸ member⟩
    exact False.elim (allowed.2.2 (coverage fiber.id count yielding fiber assigned heap found oldInstalled queued))
  · have other : id ≠ (interruptWithCause cause fiber).1.id := by
      intro equal
      exact same (equal.trans key)
    have old : machine.fiber? id = some after := by
      rw [RunMachine.fiber?_update_other _ machine id other] at actual
      exact actual
    exact held count assigned heap after old installed


/-- Actual addressed replacement retains a queued finish's drained-stack authority. -/
theorem terminal_update (machine : Effect4.Program.NativeMachine)
    (before after : Effect4.Program.SourceScope.SourceFiber) (id : FiberId)
    (found : machine.fiber? before.id = some before) (key : after.id = before.id)
    (stack : after.frame.stack = before.frame.stack) (held : TerminalStack machine id) :
    TerminalStack (machine.update after) id := by
  intro fiber actual
  by_cases same : id = before.id
  · subst id
    have self : (machine.update after).fiber? before.id = some after := by
      rw [← key]
      apply RunMachine.fiber?_update_self
      exact ⟨before, RunMachine.mem_of_fiber? found, key.symm⟩
    rw [self] at actual
    cases actual
    exact stack.trans (held before found)
  · have other : id ≠ after.id := by intro equal; exact same (equal.trans key)
    rw [RunMachine.fiber?_update_other after machine id other] at actual
    exact held fiber actual

/-- Numeric queue transport shares one assertion case split across actual metadata producers. -/
theorem command_transport_into (world next : HostTimeoutNumberConfiguration.World)
    (before after : Effect4.Program.NativeMachine) (commands : List Guard.NCmd) (command : Guard.NCmd)
    (queued : command ∈ commands) (held : CommandAt world before command)
    (replies : ∀ id token code, ReplyAt world before id token code → ReplyAt next after id token code)
    (loops : ∀ id yielding, .loop id yielding ∈ commands →
      CommandAt world before (.loop id yielding) → CommandAt next after (.loop id yielding))
    (finishes : ∀ id selected, .finish id selected ∈ commands → CommandAt world before (.finish id selected) →
      CommandAt next after (.finish id selected))
    (afterReturns : ∀ host yielding kind, .afterInterrupt host yielding kind ∈ commands →
      CommandAt world before (.afterInterrupt host yielding kind) → CommandAt next after (.afterInterrupt host yielding kind))
    (raceReturns : ∀ race host yielding remaining visited, .raceCancel race host yielding remaining visited ∈ commands →
      CommandAt world before (.raceCancel race host yielding remaining visited) →
      CommandAt next after (.raceCancel race host yielding remaining visited)) :
    CommandAt next after command := by
  cases command with
  | resume id token code => exact replies id token code held
  | loop id yielding => exact loops id yielding queued held
  | finish id selected => exact finishes id selected queued held
  | afterInterrupt host yielding kind => exact afterReturns host yielding kind queued held
  | raceCancel race host yielding remaining visited => exact raceReturns race host yielding remaining visited queued held
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


/-- The existing same-world queue transport remains an instance. -/
theorem command_transport (world : HostTimeoutNumberConfiguration.World)
    (before after : Effect4.Program.NativeMachine) (commands : List Guard.NCmd) (command : Guard.NCmd)
    (queued : command ∈ commands) (held : CommandAt world before command)
    (replies : ∀ id token code, ReplyAt world before id token code → ReplyAt world after id token code)
    (loops : ∀ id yielding, .loop id yielding ∈ commands →
      CommandAt world before (.loop id yielding) → CommandAt world after (.loop id yielding))
    (finishes : ∀ id selected, .finish id selected ∈ commands → CommandAt world before (.finish id selected) →
      CommandAt world after (.finish id selected))
    (afterReturns : ∀ host yielding kind, .afterInterrupt host yielding kind ∈ commands →
      CommandAt world before (.afterInterrupt host yielding kind) → CommandAt world after (.afterInterrupt host yielding kind))
    (raceReturns : ∀ race host yielding remaining visited, .raceCancel race host yielding remaining visited ∈ commands →
      CommandAt world before (.raceCancel race host yielding remaining visited) →
      CommandAt world after (.raceCancel race host yielding remaining visited)) :
    CommandAt world after command :=
  command_transport_into world world before after commands command queued held replies loops finishes afterReturns raceReturns

/-- The same exact fibers and store retain an existing actual cleanup wait. -/
theorem cleanup_await_fields (before after : NativeMachine) (targets : List FiberId)
    (state : after.state = before.state) (fibers : after.fibers = before.fibers)
    (previous : CleanupAwait before targets) : CleanupAwait after targets := by
  have lookup : ∀ id, after.fiber? id = before.fiber? id := by
    intro id
    change List.find? _ after.fibers = List.find? _ before.fibers
    rw [fibers]
  rcases previous with ready | ⟨attempt, member, present, complete⟩
  · exact Or.inl (state ▸ ready)
  · refine Or.inr ⟨attempt, member, ?_, ?_⟩
    · rw [lookup]; exact present
    · intro fiber actual published
      rw [lookup] at actual
      exact state ▸ complete fiber actual published

/-- The same exact fibers and store retain the legacy actual cleanup image wait. -/
theorem await_fields (before after : NativeMachine) (targets : List FiberId)
    (image : HostTimeoutNumberFlow.Image) (own : image.count = image.cleanups.length + 1)
    (state : after.state = before.state) (fibers : after.fibers = before.fibers)
    (previous : HostTimeoutNumberWait.AwaitAt image own before targets) :
    HostTimeoutNumberWait.AwaitAt image own after targets := by
  have lookup : ∀ id, after.fiber? id = before.fiber? id := by
    intro id
    change List.find? _ after.fibers = List.find? _ before.fibers
    rw [fibers]
  rcases previous with ready | ⟨attempt, member, present, complete⟩
  · exact Or.inl (state ▸ ready)
  · refine Or.inr ⟨attempt, member, ?_, ?_⟩
    · rw [lookup]; exact present
    · intro fiber actual published
      rw [lookup] at actual
      exact state ▸ complete fiber actual published

/-- Existing actual commands retain their permission through metadata fields outside the numeric observation. -/
theorem commands_fields (world : HostTimeoutNumberConfiguration.World) (before after : NativeMachine)
    (commands : List Guard.NCmd) (state : after.state = before.state) (fibers : after.fibers = before.fibers)
    (view : after.completedExits = before.completedExits) (held : Commands world before commands) :
    Commands world after commands := by
  have lookup : ∀ id, after.fiber? id = before.fiber? id := by
    intro id
    change List.find? _ after.fibers = List.find? _ before.fibers
    rw [fibers]
  intro command member
  apply command_transport world before after commands command member (held command member)
    (fun id token code good => reply_fields world before after id token code fibers state view good)
  · intro id yielding member previous context roleAt oldHeap fiber actual installedFin
    rw [state] at oldHeap
    rw [lookup] at actual
    exact previous context roleAt oldHeap fiber actual installedFin
  · intro id selected member previous
    exact ⟨fun fiber actual => previous.1 fiber ((lookup id).symm ▸ actual),
      fun role roleAt => exit_machine before after role selected state view (previous.2 role roleAt)⟩
  · intro host yielding kind member previous
    cases kind with
    | join target mode => trivial
    | race race => trivial
    | awaitAll targets =>
      exact ⟨fun image own suffix roleAt => await_fields before after targets image own state fibers (previous.1 image own suffix roleAt),
        fun suffix roleAt => cleanup_await_fields before after targets state fibers (previous.2 suffix roleAt)⟩
  · intro race host yielding remaining visited member previous
    exact ⟨fun image own suffix roleAt => await_fields before after (remaining ++ visited) image own state fibers (previous.1 image own suffix roleAt),
      fun suffix roleAt => cleanup_await_fields before after (remaining ++ visited) state fibers (previous.2 suffix roleAt)⟩

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
  exact command_transport world machine _ commands command queued held
    (fun id token code good => interrupt_reply world machine fiber cause id token code found unique good)
    (fun id yielding member good => loop_interrupt context world machine commands fiber cause id yielding
      found coverage allowed member good)
    (fun id selected member good => ⟨terminal_update machine fiber _ id found key
      (HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause).2.2.1 good.1,
      fun role assigned => exit_machine machine _ role selected rfl
        (interrupt_view machine fiber cause found unique) (good.2 role assigned)⟩)
    (by
      intro host yielding kind member good
      cases kind with
      | join target mode => trivial
      | race race => trivial
      | awaitAll targets =>
          exact ⟨fun image own suffix assigned => await_update machine fiber _ targets image own found key exit
            (good.1 image own suffix assigned),
            fun suffix assigned => cleanup_await_update machine fiber _ targets found key exit (good.2 suffix assigned)⟩)
    (by
      intro race host yielding remaining visited member good
      exact ⟨fun image own suffix assigned => await_update machine fiber _ (remaining ++ visited) image own found key exit
        (good.1 image own suffix assigned),
        fun suffix assigned => cleanup_await_update machine fiber _ (remaining ++ visited) found key exit (good.2 suffix assigned)⟩)

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
    simpa only [CountInstalled, (HostTimeoutNumberConfigurationInterrupt.interrupt_fields fiber cause).2.2.1] using installed
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
