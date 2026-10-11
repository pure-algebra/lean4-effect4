import Effect4.Laws.Program.ReleaseCustody.NativeIterationDebit
import Effect4.Laws.Program.ReleaseCustody.NativeMachineShape
import Effect4.Laws.Program.ReleaseCustody.CommandSequencing
import Effect4.Laws.Program.ReleaseCustody.NativeStacks
import Effect4.Laws.Program.ReleaseCustody.ReplySequencing
import Effect4.Laws.Program.Guard.NativeAssembly

/-!
Concept: scope-lifetime-finalization R11.
Question: actual loop command closure serves Execution.history and Workers.releases_step.
Reach: actual source-owned frames, sequential and race-free source, Guard command ownership and unique scope keys.
Limit: this command theorem supplies funding and frame sequencing; scope rows and other command cases remain separate.
Unlock: whole command induction uses the complete evaluator accounting without an arbitrary resume assumption.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.LoopCommand
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
open Effect4.Program.ReleaseCustody.Sequencing Effect4.Program.ReleaseCustody.RuntimeShape
open Effect4.Program.ReleaseCustody.CommandStacks

/-- Installing any outcome changes only the selected owner's saved stack.
Consumer: loop tail transport below. -/
theorem settle_away (id : FiberId) (rest : List NCmd) (it : RuntimeShape.Iteration)
    (key : it.fiber.id = id) : StackLinksAway id it.machine (settle id rest it).1 := by
  have outcome (next : RuntimeShape.Iteration) (same : next.fiber.id = id) :
      StackLinksAway id next.machine (settleOutcome id rest next).1 := by
    have installed := update_away next.machine (Settle.settledFiber next)
    rw [Settle.settledFiber_id, same] at installed
    rw [Settle.settleOutcome_machine]
    cases next.outcome with
    | stuck why => exact installed
    | _ => exact installed
  cases messages : it.edits with
  | nil => simpa only [settle, messages] using outcome it key
  | cons message tail =>
    have installed := update_away it.machine it.fiber
    rw [key] at installed
    have changed := (NativeStacks.lookup_links
      (Moves.InterferesWithLookup.fiberEdits (message :: tail) (it.machine.update it.fiber)).lookup).away id
    have prior := installed.trans changed
    simp only [settle, messages]
    split
    · exact prior
    · rename_i owner found
      exact prior.trans (outcome {it with
        machine := (applyFiberEdits (message :: tail) (it.machine.update it.fiber)).1
        fiber := owner
        nested := (applyFiberEdits (message :: tail) (it.machine.update it.fiber)).2 ++ it.nested
        edits := []} ((fiber_id_of_lookup found).trans key))

/-- The actual loop installs one returned owner and protects every waiting command.
Consumer: full command induction for the original Workers release history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loop (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (yielding : Bool) (rest : List NCmd)
    (guard : GuardState m) (commands : GuardQueue root table m (.loop id yielding :: rest))
    (scopes : Execution.ScopeRows m) (frames : ConfigurationKept m)
    (queue : QueueStable m (.loop id yielding :: rest))
    (source : SourceScope.ConfigurationAt root m) (fragment : SourceScope.Fragment root)
    (sequential : SourceScope.SequentialSource root) (raceFree : SourceScope.RaceFreeSource root)
    (funded : Funded q m (.loop id yielding :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.loop id yielding) rest
    Funded q out.1 out.2 ∧ ConfigurationKept out.1 ∧ QueueStable out.1 out.2 := by
  letI := evaluatorFor root table
  obtain ⟨fiber, found, running, active⟩ := commands.authority (.loop id yielding) (List.mem_cons_self ..)
  have key : fiber.id = id := fiber_id_of_lookup found
  have lookup : m.fiber? fiber.id = some fiber := by rw [key]; exact found
  have member := List.mem_of_find?_eq_some found
  have kept := frames fiber member
  have owned := (source.fibers fiber member).frame
  have state := NativeState.iteration_state root table guard fiber yielding ⟨fiber, lookup⟩
  have controls := NativeStateLinks.iteration_links root table m fiber yielding
  obtain ⟨old, afterFound, _, _, _⟩ := controls.controls.active fiber.id fiber lookup running active
  have returned := NativeSequencing.iteration_returned root table m fiber yielding active kept.sequence owned
  have same := Interruption.iteration_id root table m fiber yielding
  have debit := NativeIterationDebit.iteration q root table m fiber yielding kept.sequence fragment owned
    sequential guard.fiberIds scopes.1 scopes.2.2 (ReplySequencing.no_races root raceFree m source)
  have charged : Funded q m rest := by
    simpa only [Funded, List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] using funded
  have accounting := settle_funded q m fiber _ rest guard.fiberIds lookup state.state.fiberIds
    old afterFound same debit charged
  have machine := NativeMachineShape.iteration root table (interpOf root table) m fiber yielding frames
  have settled := CommandSequencing.settle_configuration id rest _ machine returned
  have links := (NativeStacks.iteration_links root table m fiber yielding).away id
  have tail : QueueStable (settle id rest (iteration (interpOf root table) m fiber yielding)).1 rest := by
    apply queue_tail_transport root table (.loop id yielding) rest commands
      (fun c present => queue c (List.mem_cons_of_mem _ present)) id rfl
    · exact SettleQueue.raceHostsPreserved_settle id rest _ controls.races
    · exact links.trans (settle_away id rest _ (same.trans key))
  have waiting := CommandSequencing.settle_queue root table id rest _ old (same.trans key)
    (key ▸ afterFound) (ReturnCommands.iteration_nested root table m fiber yielding (guard.frameCodes fiber member))
    returned tail
  dsimp only
  simp only [driveStep, found]
  rw [← key]
  exact ⟨accounting, key ▸ settled, key ▸ waiting⟩

/-- The actual delivery installs one returned owner and protects every waiting command.
Consumer: full command induction for the original Workers release history. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem deliver (q : List Nat) (root : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (yielding : Bool) (rest : List NCmd)
    (guard : GuardState m) (commands : GuardQueue root table m (.deliver id yielding :: rest))
    (scopes : Execution.ScopeRows m) (frames : ConfigurationKept m)
    (queue : QueueStable m (.deliver id yielding :: rest))
    (source : SourceScope.ConfigurationAt root m) (fragment : SourceScope.Fragment root)
    (sequential : SourceScope.SequentialSource root) (raceFree : SourceScope.RaceFreeSource root)
    (funded : Funded q m (.deliver id yielding :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.deliver id yielding) rest
    Funded q out.1 out.2 ∧ ConfigurationKept out.1 ∧ QueueStable out.1 out.2 := by
  letI := evaluatorFor root table
  obtain ⟨fiber, found, running, active⟩ := commands.authority (.deliver id yielding) (List.mem_cons_self ..)
  have key : fiber.id = id := fiber_id_of_lookup found
  have lookup : m.fiber? fiber.id = some fiber := by rw [key]; exact found
  have member := List.mem_of_find?_eq_some found
  have kept := frames fiber member
  have owned := (source.fibers fiber member).frame
  have state := NativeState.evaluateNative_state root table guard fiber yielding ⟨fiber, lookup⟩
  have controls := NativeStateLinks.evaluateNative_links root table m fiber yielding
  obtain ⟨old, afterFound, _, _, _⟩ := controls.controls.active fiber.id fiber lookup running active
  have returned := NativeSequencing.native_returned root table m fiber yielding active kept.sequence owned
  have same := Interruption.evaluateNative_id root table m fiber yielding
  have debit := NativeScopeDebit.native q root table m fiber yielding kept.sequence fragment owned
    sequential guard.fiberIds scopes.1 scopes.2.2 (ReplySequencing.no_races root raceFree m source)
  have charged : Funded q m rest := by
    simpa only [Funded, List.map_cons, commandCredits, List.sum_cons, Nat.zero_add] using funded
  have accounting := settle_funded q m fiber _ rest guard.fiberIds lookup state.state.fiberIds
    old afterFound same debit charged
  have machine := NativeMachineShape.native root table m fiber yielding frames
  have settled := CommandSequencing.settle_configuration id rest _ machine returned
  have links := (NativeStacks.native_links root table m fiber yielding).away id
  have tail : QueueStable (settle id rest (evaluateNative root m fiber yielding table)).1 rest := by
    apply queue_tail_transport root table (.deliver id yielding) rest commands
      (fun c present => queue c (List.mem_cons_of_mem _ present)) id rfl
    · exact SettleQueue.raceHostsPreserved_settle id rest _ controls.races
    · exact links.trans (settle_away id rest _ (same.trans key))
  have waiting := CommandSequencing.settle_queue root table id rest _ old (same.trans key)
    (key ▸ afterFound) (ReturnCommands.evaluateNative_nested root table m fiber yielding (guard.frameCodes fiber member))
    returned tail
  dsimp only
  simp only [driveStep, found]
  rw [← key]
  exact ⟨accounting, key ▸ settled, key ▸ waiting⟩

end Effect4.Program.ReleaseCustody.LoopCommand
