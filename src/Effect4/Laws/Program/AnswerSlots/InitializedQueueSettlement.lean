import Effect4.Laws.Program.AnswerSlots.InitializedQueueEmission

/-!
Concept: store-typing R4 and reactive-scheduling R12.
Question: actual native settlement joins new command permissions to the preserved old queue.
Reach: actual returned commands, addressed messages, running owner lookups and drained finished suffixes.
Limit: the command consumer and outside decision lift remain their separate shared connectors.
Consumer: the loop/deliver QueueAt laws and both crew log histories.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Actual native settlement establishes every permission in its resulting command word. -/
theorem QueueAt.settle (spec : Spec) (before : NativeMachine) (id : FiberId)
    (commands : List Guard.NCmd) (next : Moves.NIteration) (held : QueueAt spec before commands)
    (guard : Guard.GuardQueue spec.root spec.table before commands)
    (fresh : next.fiber.id ∉ commands.filterMap (Guard.commandOwner before))
    (step : Guard.NativeState.StateStep before next.machine)
    (links : Guard.NativeStateLinks.Links before next.machine)
    (refs : before.state.refs.length ≤ next.machine.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ next.machine.state.deferreds.cells.length)
    (produced : ReturnedDemand spec next) (old : Moves.NFiber)
    (lookup : next.machine.fiber? next.fiber.id = some old) (running : next.fiber.running = true)
    (key : next.fiber.id = id)
    (finished : ∀ exit, next.outcome = .finished exit → next.fiber.frame.stack = []) :
    QueueAt spec (Machine.settle id commands next).1 (Machine.settle id commands next).2 := by
  have tail := QueueAt.settle_rest spec before id commands next held guard fresh step links refs deferred
  obtain ⟨owner, ownerLookup, ownerCode, ownerStack⟩ := NativeSettlementOwner.owner id commands next old lookup running
  have state := StatePreservation.settle_state id commands next
  intro command member
  rcases NativeSettlementCommands.member id commands next command member with previous | introduced
  · exact tail command previous
  · rcases introduced with nested | evaluation | looping | delivering | finishing
    · refine ⟨?_, ?_, ?_⟩
      · intro host isLocal fiber found
        obtain ⟨same, thunk, source⟩ := produced.admin command nested host isLocal
        have actual : (Machine.settle id commands next).1.fiber? next.fiber.id = some fiber := by
          rw [← same]
          exact found
        have equal := Option.some.inj (ownerLookup.symm.trans actual)
        subst fiber
        exact ⟨thunk, ownerCode.trans source⟩
      · cases command <;> simp only [FinishEmpty]
        rename_i host exit
        exact (produced.finishFree host exit nested).elim
      · apply TrackDemand.future spec next.machine (Machine.settle id commands next).1 command (produced.track command nested)
        · rw [state]
          exact Nat.le_refl _
        · rw [state]
          exact Nat.le_refl _
    · obtain ⟨target, rfl⟩ := evaluation
      exact ordinary_demand spec _ _ (fun _ impossible => impossible.elim)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same)
    · subst command
      exact ordinary_demand spec _ _ (fun _ impossible => impossible.elim)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same)
    · subst command
      exact ordinary_demand spec _ _ (fun _ impossible => impossible.elim)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same)
    · obtain ⟨exit, outcome, rfl⟩ := finishing
      refine ⟨?_, ?_, trivial⟩
      · intro host impossible
        exact impossible.elim
      · intro fiber found
        have actual : (Machine.settle id commands next).1.fiber? next.fiber.id = some fiber := by
          rw [key]
          exact found
        have equal := Option.some.inj (ownerLookup.symm.trans actual)
        subst fiber
        exact ownerStack.trans (finished exit outcome)
end Effect4.Program.AnswerSlots.Initialized
