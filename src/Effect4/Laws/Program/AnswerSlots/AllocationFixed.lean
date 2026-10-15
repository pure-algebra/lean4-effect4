import Effect4.Laws.Program.AnswerSlots.AllocationAdministrativeFields

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared pending allocation command/history producer.
The exact pending command profile excludes operations that only application entry can emit.
Frame transport reuses the existing command theorem.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- These fixed commands can occur before actual source entry. -/
def FixedAllowed : SourceScope.SourceCommand → Prop
  | .evaluate _ | .interruptTarget _ _ _ | .finish _ _ | .drainDue | .wake _ _ => True
  | .resume _ _ code => SourceScope.TerminalReply code ∧ NoRaceReply code
  | _ => False

/-- Actual fixed pending administration retains the full machine configuration. -/
theorem PendingConfiguration.fixed (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (before : PendingConfiguration spec fragment machine) (allowed : FixedAllowed command) :
    letI := evaluatorFor spec.root spec.table
    PendingConfiguration spec fragment (driveStep (interpOf spec.root spec.table) machine command rest).1 := by
  letI := evaluatorFor spec.root spec.table
  cases command <;> simp only [FixedAllowed] at allowed
  case evaluate id =>
    simp only [driveStep]
    split
    · exact before
    · rename_i fiber found
      split
      · exact before
      · have started := PendingConfiguration.start spec fragment machine before fiber (RunMachine.mem_of_fiber? found)
        exact PendingConfiguration.fields spec fragment _ _ started rfl rfl rfl
  case resume id token code =>
    simp only [driveStep]
    split
    · exact before
    · rename_i fiber found
      split
      · rename_i parkedToken parked
        split
        · rename_i matching
          have actual : fiber.parked = .withGuard token := matching ▸ parked
          have resumed := PendingConfiguration.resume spec fragment machine before fiber
            (RunMachine.mem_of_fiber? found) token code actual allowed.1 allowed.2
          exact PendingConfiguration.fields spec fragment _ _ resumed rfl rfl rfl
        · exact before
      · exact before
  case interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact before
    · rename_i fiber found
      have interrupted := PendingConfiguration.interruption spec fragment machine before fiber
        (RunMachine.mem_of_fiber? found) (interruptCause (interpOf spec.root spec.table) who extra fiber.id)
        (clean_interrupt spec.root spec.table who extra fiber.id)
      exact PendingConfiguration.fields spec fragment _ _ interrupted rfl rfl rfl
  case finish id exit =>
    simp only [driveStep]
    split
    · exact before
    · rename_i fiber found
      exact PendingConfiguration.finish spec fragment machine before fiber (RunMachine.mem_of_fiber? found) exit
  case drainDue =>
    have fields := (pending_store_hooks spec.root spec.table machine.state.refs machine.state.deferreds.cells.length).due
      machine.state ⟨rfl, rfl⟩
    have changed := PendingConfiguration.store_fields spec fragment machine _ before fields.1 fields.2
      ⟨rfl, before.deferred.2⟩
    exact PendingConfiguration.drainOwed spec fragment _ _ changed (due_replies spec.root spec.table machine.state)
  case wake list phase =>
    have fields := (pending_store_hooks spec.root spec.table machine.state.refs machine.state.deferreds.cells.length).wake
      list phase machine.state ⟨rfl, rfl⟩
    apply PendingConfiguration.store_fields spec fragment machine _ before fields.1 fields.2
    change DeferredQuiet (machine.state.wakeList list phase).deferreds
    unfold Stores.wakeList
    split
    · rw [before.deferred.wake]
      exact before.deferred
    · exact before.deferred

/-- The existing administrative command family supplies the pending frame walk under the exact profile. -/
theorem FixedAllowed.administrative (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (machine : NativeMachine) (before : PendingConfiguration spec fragment machine)
    (command : SourceScope.SourceCommand) (allowed : FixedAllowed command) :
    AdministrativeReady spec fragment machine command := by
  cases command <;> simp only [FixedAllowed] at allowed
  case evaluate => trivial
  case resume id token code => exact before.administrative spec fragment machine id token code allowed.1 allowed.2
  case interruptTarget => trivial
  case finish id exit => exact before.terminal spec fragment machine id exit
  case drainDue => trivial
  case wake => trivial
end Effect4.Program.AnswerSlots.AllocationAdapter
