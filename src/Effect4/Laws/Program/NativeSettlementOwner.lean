import Effect4.Laws.Program.Guard.ReturnCommands

/-!
Concept: reactive-scheduling R11.
Question: pending native administrative commands retain their actual returned owner's observations.
Reach: actual settlement, its addressed message word, first lookups and a running returned owner.
Limit: command syntax permissions are supplied separately by the emitted-command producer.
Consumer: initialized QueueAt settlement and crew log histories.
-/
set_option autoImplicit false
namespace Effect4.Program.NativeSettlementOwner
open Effect4 Effect4.Machine Effect4.Program

/-- Installing a returned owner retains the actual first lookup. -/
theorem update_lookup (machine : NativeMachine) (fiber old : Moves.NFiber)
    (found : machine.fiber? fiber.id = some old) : (machine.update fiber).fiber? fiber.id = some fiber := by
  rw [Guard.fiber_lookup_update, found]
  simp only [Option.map_some, Guard.fiber_id_of_lookup found, ↓reduceIte]

/-- Outcome disposition changes no current code or saved stack of its returned owner. -/
theorem settled_frame (next : Moves.NIteration) : (Guard.Settle.settledFiber next).frame = next.fiber.frame := by
  unfold Guard.Settle.settledFiber
  split
  · split <;> rfl
  · rfl
  · rfl

/-- Actual outcome settlement retains the installed parent's current code and saved suffix. -/
theorem outcome_owner (id : FiberId) (rest : List Guard.NCmd) (next : Moves.NIteration)
    (old : Moves.NFiber) (found : next.machine.fiber? next.fiber.id = some old) :
    ∃ row, (settleOutcome id rest next).1.fiber? next.fiber.id = some row ∧
      row.frame.current = next.fiber.frame.current ∧ row.frame.stack = next.fiber.frame.stack := by
  have installed : (next.machine.update (Guard.Settle.settledFiber next)).fiber? next.fiber.id =
      some (Guard.Settle.settledFiber next) := by
    have lookup : next.machine.fiber? (Guard.Settle.settledFiber next).id = some old := by
      rw [Guard.Settle.settledFiber_id]
      exact found
    simpa only [Guard.Settle.settledFiber_id] using update_lookup next.machine (Guard.Settle.settledFiber next) old lookup
  refine ⟨Guard.Settle.settledFiber next, ?_, congrArg (fun frame => frame.current) (settled_frame next),
    congrArg (fun frame => frame.stack) (settled_frame next)⟩
  rw [Guard.Settle.settleOutcome_machine]
  cases next.outcome <;> exact installed

/-- The existing message word preserves a running owner's current code and every saved continuation. -/
theorem owner (id : FiberId) (rest : List Guard.NCmd) (next : Moves.NIteration)
    (old : Moves.NFiber) (found : next.machine.fiber? next.fiber.id = some old) (running : next.fiber.running = true) :
    ∃ row, (settle id rest next).1.fiber? next.fiber.id = some row ∧
      row.frame.current = next.fiber.frame.current ∧ row.frame.stack = next.fiber.frame.stack := by
  cases edits : next.edits with
  | nil =>
    simp only [settle, edits]
    exact outcome_owner id rest next old found
  | cons edit tail =>
    have installed := update_lookup next.machine next.fiber old found
    obtain ⟨fiber, seen, word⟩ := (Moves.InterferesWithLookup.fiberEdits (edit :: tail) (next.machine.update next.fiber)).lookup
      next.fiber.id next.fiber installed
    have current := (word.controls (.inl running)).1
    simp only [settle, edits, seen]
    have lookup : (applyFiberEdits (edit :: tail) (next.machine.update next.fiber)).1.fiber? fiber.id = some fiber := by
      rw [word.id]
      exact seen
    obtain ⟨row, final, code, stack⟩ := outcome_owner id rest
      {next with
        machine := (applyFiberEdits (edit :: tail) (next.machine.update next.fiber)).1
        fiber := fiber
        nested := (applyFiberEdits (edit :: tail) (next.machine.update next.fiber)).2 ++ next.nested
        edits := []}
      fiber lookup
    rw [word.id] at final
    exact ⟨row, final, code.trans current, stack.trans word.stack⟩
end Effect4.Program.NativeSettlementOwner
