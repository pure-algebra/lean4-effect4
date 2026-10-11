import Effect4.Laws.Program.ReleaseCustody.Execution
import Effect4.Laws.Program.Guard.Core

/-!
Concept: scope-lifetime-finalization, R11, at most one release per registration.
Question: scheduler edits consumed by `ReleaseCustody.Execution.outer_custody`.
Reach: actual native machines and arbitrary programs, tables and command budgets.
The supplied command contract remains a premise; these edits prove no progress or source uniqueness.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Effect4.Program.ReleaseCustody.OuterProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control Effect4.Program.ReleaseCustody.Execution

/-- A disarm changes none of the custody fields. -/
theorem disarm (q : List Nat) (m : NativeMachine) (owner : FiberId) (held : Ready q m) :
    Ready q (m.disarm owner) :=
  ⟨ForkLedger.Invariant.disarm_ok held.fibers owner, held.scopes, held.pending,
    held.dispatcher, held.funded⟩

/-- A store edit outside the scopes retains the same custody. -/
theorem state (q : List Nat) (m : NativeMachine) (next : Stores) (held : Ready q m)
    (scopes : next.scopes = m.state.scopes) (supply : next.nextName = m.state.nextName) :
    Ready q {m with state := next} := by
  refine ⟨held.fibers, ?_, held.pending, held.dispatcher, ?_⟩
  · simpa only [ScopeRows, Stores.ScopeKeysFresh, scopes, supply] using held.scopes
  · simpa only [Funded, machineCredits, scopes] using held.funded

/-- Draining a dispatcher discards zero-credit tasks and retains their snapshot assertion. -/
theorem drain (q : List Nat) (m : NativeMachine) (owner : FiberId) (fiber : Fiber)
    (held : Ready q m) (found : m.fiber? owner = some fiber) :
    Ready q ((m.update {fiber with dispatcher := fiber.dispatcher.drain.2}).disarm owner) ∧
      TasksZero q fiber.dispatcher.drain.1 := by
  have member := List.mem_of_find?_eq_some found
  have found' : m.fiber? fiber.id = some fiber := by
    rw [fiber_id_of_lookup found]
    exact found
  have changed := ready_update q m fiber {fiber with dispatcher := fiber.dispatcher.drain.2}
    held found' rfl (held.pending fiber member) (by
      intro bucket present
      exact False.elim (List.not_mem_nil present)) (by
      simp only [fiberCredits, Dispatcher.drain, List.map_nil, List.sum_nil, Nat.add_zero]
      omega)
  refine ⟨disarm q _ owner changed, ?_⟩
  intro task present
  obtain ⟨tasks, listed, present⟩ := List.mem_flatten.mp present
  obtain ⟨bucket, bucketPresent, rfl⟩ := List.mem_map.mp listed
  exact held.dispatcher fiber member bucket bucketPresent task present

/-- A scheduler verdict changes no stored code or pending continuation. -/
theorem yield (q : List Nat) (m : NativeMachine) (id : FiberId) (verdict : Bool)
    (held : Ready q m) : Ready q (m.modify id fun f => {f with yieldOverride := some verdict}) := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i fiber found
    have member := List.mem_of_find?_eq_some found
    have found' : m.fiber? fiber.id = some fiber := by
      rw [fiber_id_of_lookup found]
      exact found
    exact ready_update q m fiber _ held found' rfl (held.pending fiber member)
      (held.dispatcher fiber member) (Nat.le_refl _)

/-- Interrupt recording clears pending entries or leaves them unchanged and never creates a credit. -/
theorem interrupt (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (target : FiberId) (fiber : Fiber)
    (held : Ready q m) (found : m.fiber? target = some fiber) :
    Ready q (Lift.interruptEdit (interpOf root table) m who extra target fiber) := by
  have member := List.mem_of_find?_eq_some found
  let interp := interpOf root table
  have key : (interruptRecord interp who extra fiber).1.id = fiber.id := by
    unfold interruptRecord
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
    split
    · rfl
    · cases fiber.frame.interruptedCause <;> dsimp only
      all_goals
        split
        · split <;> rfl
        · rfl
  have pending : ∀ p ∈ (interruptRecord interp who extra fiber).1.pending,
      p.resumeWith = .exitsValue ∨ p.resumeWith = .void ∨
        ∃ exit, p.resumeWith = .continueWith (.restore exit) := by
    unfold interruptRecord
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
    split
    · exact held.pending fiber member
    · cases fiber.frame.interruptedCause <;> dsimp only
      all_goals
        split
        · split
          · exact held.pending fiber member
          · intro p present
            exact False.elim (List.not_mem_nil present)
        · exact held.pending fiber member
  have dispatcher : ∀ bucket ∈ (interruptRecord interp who extra fiber).1.dispatcher.buckets,
      TasksZero q bucket.tasks := by
    unfold interruptRecord
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
    split
    · exact held.dispatcher fiber member
    · cases fiber.frame.interruptedCause <;> dsimp only
      all_goals
        split
        · split <;> exact held.dispatcher fiber member
        · exact held.dispatcher fiber member
  have credit : fiberCredits q (interruptRecord interp who extra fiber).1 ≤ fiberCredits q fiber := by
    unfold interruptRecord
    dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
      FiberCore.setDeferred, FiberCore.answerWith, FiberCore.failure, frameCore]
    split
    · exact Nat.le_refl _
    · cases fiber.frame.interruptedCause <;> dsimp only
      all_goals
        split
        · split
          · exact Nat.le_refl _
          · exact Evaluation.failure_fiber_le q fiber _
        · exact Nat.le_refl _
  have emit1 := ready_emit q m [.interruptRecorded who target] held rfl rfl
  have emit2 := ready_emit q _ [.interruptDeferred target] emit1 rfl rfl
  have found' : m.fiber? fiber.id = some fiber := by
    rw [fiber_id_of_lookup found]
    exact found
  unfold Lift.interruptEdit
  dsimp only
  split
  · exact ready_update q _ fiber _ emit2 found' key pending dispatcher credit
  · exact ready_update q _ fiber _ emit1 found' key pending dispatcher credit

/-- A completion creates no foreign release credit. -/
theorem completion_zero (q : List Nat) (answer : Completion Val Err Defect FiberId Ann) :
    currentCredits q (embed (completionPrim answer)) = 0 := by
  cases answer with
  | ofExit exit => cases exit <;> rfl
  | ofRefGet cell => rfl

/-- Native answer preparation changes only the external allocation table. -/
theorem prepare_fields (q : List Nat) (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (store : Stores) :
    (prepareExternalAnswer table current answer store).1.scopes = store.scopes ∧
      (prepareExternalAnswer table current answer store).1.nextName = store.nextName ∧
      currentCredits q (prepareExternalAnswer table current answer store).2 = 0 := by
  unfold prepareExternalAnswer
  dsimp only
  split
  · exact ⟨rfl, rfl, completion_zero q answer⟩
  · split
    · split
      · exact ⟨rfl, rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl, rfl⟩
        · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, completion_zero q answer⟩


/-- Native clock advancement changes only the timer store. -/
theorem clock_fields (root : NativeEff) (table : RowTable) (millis : ClockMillis) (store : Stores) :
    ((interpOf root table).clockStep millis store).2.scopes = store.scopes ∧
      ((interpOf root table).clockStep millis store).2.nextName = store.nextName := ⟨rfl, rfl⟩

/-- The timer resumes inline with the fixed successful unit, which carries no release credit. -/
theorem clock_owed (root : NativeEff) (table : RowTable) (q : List Nat) (millis : ClockMillis)
    (store : Stores) (owed : Owed NCode)
    (found : ((interpOf root table).clockStep millis store).1 = some owed) :
    currentCredits q owed.code = 0 ∧ owed.mode = .now := by
  change ((store.timers.clockStep millis (Completion.ofExit (Exit.success Val.unit) :
    Completion Val Err Defect FiberId Ann)).1.map
      (Owed.mapCode (fun c => embed (completionPrim c)))) = some owed at found
  obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
  have facts := TimerStore.clockStep_owed store.timers millis
    (Completion.ofExit (Exit.success Val.unit) : Completion Val Err Defect FiberId Ann) original originalFound
  exact ⟨completion_zero q original.code, facts.2⟩

/-- Preparing any completion retains readiness and creates a zero-credit resume command. -/
theorem prepare (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (held : Ready q m) :
    Ready q {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1} ∧
      currentCredits q (prepareAsyncAnswer (interpOf root table) m id token answer).2 = 0 := by
  unfold prepareAsyncAnswer
  split
  · exact ⟨held, completion_zero q answer⟩
  · refine ⟨state q m _ held ?_ ?_, ?_⟩
    · exact (prepare_fields q table _ answer m.state).1
    · exact (prepare_fields q table _ answer m.state).2.1
    · exact (prepare_fields q table _ answer m.state).2.2

/-- A zero-credit command list consumes no additional registration budget. -/
theorem queue (q : List Nat) (m : NativeMachine) (commands : List Control.Command)
    (held : Ready q m) (zero : (commands.map (commandCredits q)).sum = 0) :
    Funded q m commands := by
  have funded := held.funded
  simpa only [Funded, zero, List.map_nil, List.sum_nil] using funded

/-- A dispatcher task has exactly its resume code's credit. -/
theorem task_commands (q : List Nat) (task : Task EffName EffThunk Val Err Defect FiberId Ann) :
    ((taskCmds task).map (commandCredits q)).sum = taskCredits q task := by
  cases task <;>
    simp only [taskCmds, taskCredits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      commandCredits, Nat.add_zero]

/-- Every actual scheduler edit satisfies the existing decision lift.
The native command contract remains explicit, so this helper adds no reachability assumption. -/
theorem build (root : NativeEff) (table : RowTable) (q : List Nat) :
    letI := evaluatorFor root table
    CommandContract root table q →
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => Ready q m) (fun _ m commands => Funded q m commands)
      (fun _ _ => TasksZero q)
      (fun _ m decision => Run.Accepted table (Api.HostSession.callTable root table) m decision) := by
  letI := evaluatorFor root table
  intro commands
  refine {
    step := commands
    nil := ?_
    evaluate := ?_
    drain := ?_
    ran := ?_
    task := ?_
    skip := ?_
    yield := ?_
    interrupt := ?_
    middleware := ?_
    clockNone := ?_
    clockSome := ?_
    answer := ?_ }
  · intro _ _ task present
    exact False.elim (List.not_mem_nil present)
  · intro _ m id held _
    exact queue q m [.evaluate id, .drainDue] held rfl
  · intro _ m owner fiber held found
    exact drain q m owner fiber held found
  · intro _ m owner task held
    exact ready_emit q m [.ranTask owner task] held rfl rfl
  · intro _ m owner task rest held _ snapshot
    refine ⟨queue q _ _ (ready_emit q m [.ranTask owner task] held rfl rfl) ?_, ?_⟩
    · rw [task_commands]
      exact snapshot task List.mem_cons_self
    · intro tail present
      exact snapshot tail (List.mem_cons_of_mem task present)
  · intro _ _ task rest snapshot tail present
    exact snapshot tail (List.mem_cons_of_mem task present)
  · intro _ m id verdict held
    exact yield q m id verdict held
  · intro _ m who extra target fiber held found
    exact interrupt root table q m who extra target fiber held found
  · intro _ m held
    exact ⟨held.fibers, held.scopes, held.pending, held.dispatcher, held.funded⟩
  · intro _ m millis next held _ clock
    have fields := clock_fields root table millis m.state
    rw [clock] at fields
    exact ⟨(), trivial, state q m next held fields.1 fields.2⟩
  · intro _ m millis owed next held _ clock
    have fields := clock_fields root table millis m.state
    rw [clock] at fields
    have ready := state q m next held fields.1 fields.2
    have owedFacts := clock_owed root table q millis m.state owed (congrArg Prod.fst clock)
    refine ⟨(), trivial, ?_, ?_⟩
    · simpa only [drainOwed, owedFacts.2] using ready
    · intro _
      simp only [drainOwed, owedFacts.2, List.cons_append, List.nil_append]
      apply queue q _ _ ready
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, commandCredits,
        owedFacts.1, Nat.add_zero]
  · intro w m id token answer held live _
    have prepared := prepare root table q m id token answer held
    apply commands [] w {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1}
      (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2)
      [.drainDue] live
    refine ⟨prepared.1, fun _ => ⟨queue q _ _ prepared.1 ?_, ?_⟩⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, commandCredits,
        prepared.2, Nat.add_zero]
    · intro task present
      exact False.elim (List.not_mem_nil present)

end Effect4.Program.ReleaseCustody.OuterProbe

