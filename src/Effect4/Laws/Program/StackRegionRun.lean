import Effect4.Laws.Program.StackRegionCommands
import Effect4.Laws.Program.MaskBracket
import Effect4.Laws.Machine.LiftPrefix
import Effect4.Laws.Machine.Handshake

/-!
Concept: scope-lifetime-finalization, R11, the saved-mask region bracket.
Question: derive compiled_region_bracket's entry-stack shape from its actual command prefix.
Reach: compiled LoopCut entry, every finite budget, and each executed detached evaluation before its exit.
Limit: crossing the detached exit ends this region; the law supplies no progress or cleanup count.
Consumer: the saved-mask region bracket, then protected permits and Pool use.
-/
set_option autoImplicit false
namespace Effect4.Program.StackRegion
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves Effect4.FrameFiber

/-- Distinct actual stored identities give the entry suffix at the watched starting row. -/
theorem entry_held (root : NativeEff) (table : RowTable) {bases : List Bool}
    {machine : NativeMachine} {commands : List NCommand} (entry : LoopCut root table bases machine commands)
    (id : FiberId) (fiber : NFiber) (found : machine.fiber? id = some fiber) :
    Held id fiber.frame.stack machine := by
  refine ⟨?_, ?_⟩
  · rw [← Guard.fiber_id_of_lookup found]
    exact entry.state.fibersBelow fiber (List.mem_of_find?_eq_some found)
  · intro other member selected live
    have lookup := fiber_lookup_of_mem_nodup machine entry.state.fiberIds other member
    rw [selected] at lookup
    have same : other = fiber := Option.some.inj (lookup.symm.trans found)
    subst other
    exact ⟨[], rfl⟩

/-- A checked entry suffix becomes a region at the actual stored row.
Consumer: Timeout's counted attempt retains its onExit beneath the count callback. -/
theorem entry_suffix_held (root : NativeEff) (table : RowTable) {bases : List Bool}
    {machine : NativeMachine} {commands : List NCommand} (entry : LoopCut root table bases machine commands)
    (id : FiberId) (fiber : NFiber) (found : machine.fiber? id = some fiber)
    (below : List NCode) (inside : Inside below fiber) : Held id below machine := by
  have whole := entry_held root table entry id fiber found
  refine ⟨whole.allocated, ?_⟩
  intro other member selected live
  obtain ⟨above, old⟩ := whole.frames other member selected live
  obtain ⟨own, suffix⟩ := inside
  exact ⟨above ++ own, by rw [old, suffix, List.append_assoc]⟩

/-- The compiled queue rules out clearing a live row without adding an owner assumption. -/
theorem command_clear (root : NativeEff) (table : RowTable) (machine : NativeMachine)
    (head : NCommand) (rest : List NCommand) (queue : Guard.GuardQueue root table machine (head :: rest)) :
    ∀ target, head = .exitDone target → ∀ fiber, machine.fiber? target = some fiber → fiber.exit ≠ none := by
  intro target same fiber found live
  subst head
  obtain ⟨actual, lookup, exited⟩ := queue.authority _ (List.mem_cons_self ..)
  cases lookup.symm.trans found
  rw [live] at exited
  cases exited

/-- An actual allowed command prefix retains the region and both compiled cuts.
The allowed predicate reads the detached evaluation, not a resulting stack-shape assertion. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem drive (root : NativeEff) (table : RowTable) {bases : List Bool}
    (machine : NativeMachine) (commands : List NCommand) (id : FiberId) (below : List NCode)
    (fuel : Nat) (entry : LoopCut root table bases machine commands) (held : Held id below machine)
    (permitted : Lift.PrefixAllows (evaluator := evaluatorFor root table) (interpOf root table)
      (fun next head _ => Continues root table (interpOf root table) id below next head) fuel machine commands) :
    let out := driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel machine commands
    Held id below out.1 ∧ ∃ laterBases, bases <+: laterBases ∧ LoopCut root table laterBases out.1 out.2 := by
  letI := evaluatorFor root table
  apply Lift.driveState_lift_allowed (interpOf root table)
    (fun next pending => Held id below next ∧
      ∃ laterBases, bases <+: laterBases ∧ LoopCut root table laterBases next pending)
    (fun next head _ => Continues root table (interpOf root table) id below next head)
  · intro next head rest _ going current
    obtain ⟨currentBases, grown, cut⟩ := current.2
    obtain ⟨laterBases, grown', later⟩ := cut.step
    exact ⟨command root table (interpOf root table) next head rest id below current.1 going
      (command_clear root table next head rest cut.queue), laterBases, grown.trans grown', later⟩
  · exact ⟨held, bases, List.prefix_refl _, entry⟩
  · exact permitted

/-- A checked local prefix supplies the entry of the remaining region execution.
The boundary premise names each actual detached evaluation before its exit.
Consumer: numeric attempt entry, without a fixed scenario-budget partition. -/
theorem drive_from_prefix (root : NativeEff) (table : RowTable) {bases : List Bool}
    (machine : NativeMachine) (commands : List NCommand) (prefixFuel remainingFuel : Nat)
    (entered : NativeMachine) (pending : List NCommand)
    (entry : LoopCut root table bases machine commands)
    (ran : driveState (evaluator := evaluatorFor root table) (interpOf root table)
      prefixFuel machine commands = (entered, pending))
    (id : FiberId) (fiber : NFiber) (found : entered.fiber? id = some fiber)
    (below : List NCode) (inside : Inside below fiber)
    (permitted : Lift.PrefixAllows (evaluator := evaluatorFor root table) (interpOf root table)
      (fun next head _ => Continues root table (interpOf root table) id below next head)
      remainingFuel entered pending) :
    let out := driveState (evaluator := evaluatorFor root table) (interpOf root table)
      (prefixFuel + remainingFuel) machine commands
    Held id below out.1 ∧ ∃ laterBases, bases <+: laterBases ∧ LoopCut root table laterBases out.1 out.2 := by
  letI := evaluatorFor root table
  obtain ⟨entryBases, grown, cut⟩ := entry.drive prefixFuel
  rw [ran] at cut
  have region := drive root table entered pending id below remainingFuel cut
    (entry_suffix_held root table cut id fiber found below inside) permitted
  dsimp only
  rw [driveState_add _ prefixFuel remainingFuel, ran]
  obtain ⟨kept, laterBases, laterGrown, later⟩ := region
  exact ⟨kept, laterBases, grown.trans laterGrown, later⟩

/-- The suffix determines its region-owned prefix without choosing a witness. -/
theorem inside_take {below : List NCode} {fiber : NFiber} (held : Inside below fiber) :
    fiber.frame.stack = fiber.frame.stack.take (fiber.frame.stack.length - below.length) ++ below := by
  obtain ⟨above, shape⟩ := held
  rw [shape, List.length_append, Nat.add_sub_cancel_right, List.take_left]

/-- The existing bracket now reads an actual command prefix with no supplied stack-shape premise.
The explicit boundary premise excludes exactly an executed detached evaluation that finishes. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem compiled_region_bracket_of_prefix (root : NativeEff) (table : RowTable)
    {bases : List Bool} {machine laterMachine : NativeMachine} {commands laterCommands : List NCommand}
    (entry : LoopCut root table bases machine commands) (fuel : Nat)
    (ran : driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel machine commands =
      (laterMachine, laterCommands))
    {id : FiberId} {first last : NFiber} (found : machine.fiber? id = some first)
    (found' : laterMachine.fiber? id = some last)
    (permitted : Lift.PrefixAllows (evaluator := evaluatorFor root table) (interpOf root table)
      (fun next head _ => Continues root table (interpOf root table) id first.frame.stack next head)
      fuel machine commands)
    {head laterHead : NCommand} (pending : head ∈ commands) (pending' : laterHead ∈ laterCommands)
    (steps : Steps id head) (steps' : Steps id laterHead)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV)
    (unanswered : ((detach first.frame.stack last).frame.getCont demand skip cause).answer = .empty) :
    RegionEnds first.frame last.frame
      (last.frame.stack.take (last.frame.stack.length - first.frame.stack.length)) demand skip cause := by
  have checked := drive root table machine commands id first.frame.stack fuel entry
    (entry_held root table entry id first found) permitted
  rw [ran] at checked
  obtain ⟨kept, laterBases, grown, later⟩ := checked
  have inside := kept.frames last (List.mem_of_find?_eq_some found') (Guard.fiber_id_of_lookup found')
    (later.live pending' steps' found')
  exact compiled_region_bracket root table entry later grown pending pending' steps steps' found found'
    (inside_take inside) demand skip cause unanswered

end Effect4.Program.StackRegion
