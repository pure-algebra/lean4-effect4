import Test.Dogfood.Proofs.HostTimeoutNumberObserverMap
import Effect4.Laws.Machine.ContextualMessages

/-!
Concepts: reactive-scheduling R9 and scope-lifetime-finalization R11.
Question: actual addressed message words retain one joined numeric machine, queue, and detached snapshot.
Consumer: the native settlement component of the coupled Timeout command producer.
Reach: actual message lookups, interruption-only causes, unique fiber ids, and protected prefix owners.
Limit: the source-native producer must supply its actual message admission and initial assertions.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberMessages
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutState HostTimeoutNumberConfiguration HostTimeoutNumberConfigurationTransport
open HostTimeoutNumberQueueInterrupt

abbrev Context := MessageContext × List NTask

/-- Detached tasks travel with the machine assertion through the actual addressed message word. -/
def P (context : Context) (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine) : Prop :=
  Configuration world machine ∧ Snapshot world machine context.2 ∧ (machine.fibers.map (·.id)).Nodup

/-- The same pending queue retains its numeric obligations and protected prefix owners. -/
def Q (context : Context) (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (commands : List Guard.NCmd) : Prop :=
  Commands world machine commands ∧ Protects context.1 world machine commands

/-- One observer-field map retains the joined assertions without changing the proof world. -/
theorem observer_map (context : Context) (world : HostTimeoutNumberConfiguration.World)
    (machine : Effect4.Program.NativeMachine) (commands : List Guard.NCmd)
    (observers : Effect4.Program.SourceScope.SourceFiber → List Observer)
    (held : P context world machine) (queued : Q context world machine commands) :
    P context world (HostTimeoutNumberObserverMap.mapped machine observers) ∧
      Q context world (HostTimeoutNumberObserverMap.mapped machine observers) commands := by
  exact ⟨⟨HostTimeoutNumberObserverMap.configuration world machine observers held.1,
    snapshot_replies world machine _ context.2 (HostTimeoutNumberObserverMap.reply world machine observers) held.2.1,
    by rw [HostTimeoutNumberObserverMap.ids]; exact held.2.2⟩,
    HostTimeoutNumberObserverMap.commands world machine observers commands queued.1,
    HostTimeoutNumberObserverMap.protects context.1 world machine observers commands queued.2⟩

/-- Actual addressed messages use the existing shared word producer with one common numeric world. -/
theorem admitted (order : Effect4.Laws.Effects.WorldOrder HostTimeoutNumberConfiguration.World) :
    ContextualMessages.Admitted (order := order) (P := P) (Q := Q)
      (fun context message => MessageAllowed context.1 message) := by
  constructor
  intro context world message machine commands allowed held queued
  refine ⟨world, order.refl world, ?_⟩
  cases message with
  | dropToken token =>
      rw [applyFiberEdit, HostTimeoutNumberObserverMap.drop_mapped, List.append_nil]
      exact observer_map context world machine commands _ held queued
  | observe target observer =>
      simp only [applyFiberEdit, List.append_nil]
      cases found : machine.fiber? target with
      | none =>
          simpa only [RunMachine.observe, RunMachine.modify, found] using And.intro held queued
      | some fiber =>
          rw [HostTimeoutNumberObserverMap.observe_mapped machine target observer fiber found held.2.2]
          exact observer_map context world machine commands _ held queued
  | interrupt target cause =>
      cases found : machine.fiber? target with
      | none => simpa only [applyFiberEdit, found, List.append_nil] using And.intro held queued
      | some fiber =>
          have key := RunMachine.id_of_fiber? found
          subst target
          obtain ⟨configuration, commandsGood, detached, protection⟩ := interrupt_joint context.1 world machine commands
            context.2 fiber cause found held.2.2 held.1 queued.1 held.2.1 queued.2 allowed
          simp only [applyFiberEdit, found]
          refine ⟨⟨configuration, detached, ?_⟩, commandsGood, protection⟩
          have keys : ((machine.update (interruptWithCause cause fiber).1).fibers.map (·.id)) =
              machine.fibers.map (·.id) := RunMachine.update_keeps_ids _ machine
          rw [keys]
          exact held.2.2

/-- The actual admitted word returns the same joined numeric assertions through the shared fold. -/
theorem apply_word (order : Effect4.Laws.Effects.WorldOrder HostTimeoutNumberConfiguration.World)
    (context : Context) (world : HostTimeoutNumberConfiguration.World) (machine : Effect4.Program.NativeMachine)
    (messages : List (FiberEdit Err Defect FiberId Ann))
    (allowed : ∀ message ∈ messages, MessageAllowed context.1 message)
    (held : P context world machine) (queued : Q context world machine []) :
    ∃ next, order.le world next ∧ P context next (applyFiberEdits messages machine).1 ∧
      Q context next (applyFiberEdits messages machine).1 (applyFiberEdits messages machine).2 :=
  (admitted order).apply context world messages allowed machine held queued

end Test.Dogfood.Proofs.HostTimeoutNumberMessages
