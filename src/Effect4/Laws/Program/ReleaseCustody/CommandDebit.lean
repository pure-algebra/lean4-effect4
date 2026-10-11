import Effect4.Laws.Program.ReleaseCustody.Lift
import Effect4.Laws.Program.ReleaseCustody.CommandStackSteps

/-!
Concept: scope-lifetime-finalization R11, serving `ReleaseCustody.Execution.history`.
Consumers: the actual non-evaluator command cases of admitted release custody.
A command spends its queued credit when it replaces a saved continuation.
These local debits do not establish command ownership, history closure or progress.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Effect4.Program.ReleaseCustody.CommandDebit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.ReleaseCustody.Control Effect4.Program.ReleaseCustody.Sequencing

/-- Discarding an unexecuted command cannot increase the required credit. -/
theorem tail (q : List Nat) (m : NativeMachine) (command : Command) (rest : List Command)
    (held : Funded q m (command :: rest)) : Funded q m rest := by
  simp only [Funded, List.map_cons, List.sum_cons] at held ⊢
  omega

/-- Replacing a queue by one with no greater credit retains funding. -/
theorem queue (q : List Nat) (m : NativeMachine) (before after : List Command)
    (held : Funded q m before)
    (cost : (after.map (commandCredits q)).sum ≤ (before.map (commandCredits q)).sum) :
    Funded q m after := by
  unfold Funded at held ⊢
  omega

/-- Administrative trace events contain neither a release start nor a registration. -/
theorem emit (q : List Nat) (m : NativeMachine) (commands : List Command)
    (held : Funded q m commands) (events : List ReleaseTrace.Event)
    (starts : events.countP (ReleaseTrace.releaseAt q) = 0)
    (registrations : events.countP (ReleaseTrace.registeredAt q) = 0) :
    Funded q (m.emit events) commands := by
  unfold Funded at held ⊢
  rw [emit_credits, RunMachine.emit_trace, List.countP_append, List.countP_append,
    starts, registrations, Nat.add_zero, Nat.add_zero]
  exact held

/-- Replacing one existing fiber spends at most its own and the old queue's credit. -/
theorem update (q : List Nat) (m : NativeMachine) (old next : Fiber)
    (before after : List Command) (held : Funded q m before)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? old.id = some old)
    (key : next.id = old.id)
    (debit : fiberCredits q next + (after.map (commandCredits q)).sum ≤
      fiberCredits q old + (before.map (commandCredits q)).sum) : Funded q (m.update next) after := by
  have changed := update_credits q m old next unique (List.mem_of_find?_eq_some found) key
  unfold Funded at held ⊢
  change m.trace.countP (ReleaseTrace.releaseAt q) + machineCredits q (m.update next) +
    (after.map (commandCredits q)).sum ≤ m.trace.countP (ReleaseTrace.registeredAt q)
  omega

/-- An administrative edit spends no credit when it decreases the edited fiber's credit. -/
theorem modify (q : List Nat) (m : NativeMachine) (id : FiberId) (edit : Fiber → Fiber)
    (commands : List Command) (held : Funded q m commands)
    (unique : (m.fibers.map RunFiber.id).Nodup) (key : ∀ f, (edit f).id = f.id)
    (debit : ∀ f, fiberCredits q (edit f) ≤ fiberCredits q f) :
    Funded q (m.modify id edit) commands := by
  unfold RunMachine.modify
  split
  · exact held
  · rename_i fiber found
    apply update q m fiber (edit fiber) commands commands held unique
      (by simpa only [fiber_id_of_lookup found] using found) (key fiber)
    exact Nat.add_le_add_right (debit fiber) _

/-- Code replacement cannot create response credit when no registration callback is pending. -/
theorem replace_code (q : List Nat) (fiber : Fiber) (code : NCode)
    (noAdd : NoAdd fiber.frame.stack) (zero : currentCredits q code = 0) :
    fiberCredits q {fiber with frame := {fiber.frame with current := code}} ≤ fiberCredits q fiber := by
  unfold fiberCredits
  dsimp only
  rw [noAdd_full q code _ noAdd, noAdd_full q fiber.frame.current _ noAdd, zero]
  omega

/-- Recording an interruption only discards active response credit. -/
theorem interrupt_record (root : NativeEff) (table : RowTable) (q : List Nat)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (fiber : Fiber) :
    fiberCredits q (interruptRecord (interpOf root table) who extra fiber).1 ≤ fiberCredits q fiber := by
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

/-- Starting a fiber changes counters and running status without spending release credit. -/
theorem evaluate (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (rest : List Command) (unique : (m.fibers.map RunFiber.id).Nodup)
    (held : Funded q m (.evaluate id :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.evaluate id) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · rename_i fiber found
    split
    · exact tail q m _ rest held
    · apply emit q _ _ _ _ rfl rfl
      apply update q m fiber {fiber with running := true, currentOpCount := 0}
        (.evaluate id :: rest) (.loop id false :: rest) held unique
        (by simpa only [fiber_id_of_lookup found] using found) rfl
      exact Nat.le_refl _

/-- Both stale and matched resumes obey the actual command debit. -/
theorem resume (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (token : Nat) (answer : NCode) (rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (stable : ∀ fiber, m.fiber? id = some fiber → fiber.parked = .withGuard token →
      StableFrames fiber.frame.stack)
    (held : Funded q m (.resume id token answer :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.resume id token answer) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  cases found : m.fiber? id with
  | none => simpa only [driveStep, found] using tail q m _ rest held
  | some fiber =>
    cases parked : fiber.parked with
    | notParked => simpa only [driveStep, found, parked] using tail q m _ rest held
    | withGuard actual =>
      by_cases keyEqual : actual = token
      · subst actual
        exact resume_command root table q m id token answer rest fiber found parked unique
          (stable fiber found parked) held
      · simpa only [driveStep, found, parked, if_neg keyEqual] using tail q m _ rest held

/-- An interrupt command records at most the old fiber's credit. -/
theorem interrupt (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (held : Funded q m (.interruptTarget id who extra :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.interruptTarget id who extra) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · rename_i fiber found
    apply emit q _ _ _ _ rfl rfl
    apply update q m fiber _ (.interruptTarget id who extra :: rest) _ held unique
      (by simpa only [fiber_id_of_lookup found] using found) (interruptRecord_id root table who extra fiber)
    have debit := interrupt_record root table q who extra fiber
    split <;> simpa only [List.cons_append, List.nil_append, List.map_cons, List.sum_cons,
      commandCredits, Nat.zero_add] using Nat.add_le_add_right debit ((rest.map (commandCredits q)).sum)

/-- Every native wait code starts without foreign release credit. -/
theorem await_zero (root : NativeEff) (table : RowTable) (q : List Nat)
    (m : NativeMachine) (kind : ParkKind) :
    currentCredits q (awaitCode (interpOf root table) m kind) = 0 := by
  have exit_zero (exit : ExitV) (mode : Supervision.ObserverMode) :
      currentCredits q ((interpOf root table).exitValue exit mode) = 0 := by
    cases mode
    · rfl
    · exact Evaluation.exit_credits q exit
  unfold awaitCode
  split
  · split
    · exact exit_zero _ _
    · rfl
  · rfl

/-- Wrapping an await with the void continuation creates no foreign release credit. -/
theorem await_void_zero (root : NativeEff) (table : RowTable) (q : List Nat)
    (m : NativeMachine) (kind : ParkKind) :
    currentCredits q (asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind)) = 0 :=
  await_zero root table q m kind

/-- A command-owned await overwrite consumes no credit from a callback-free stack. -/
theorem after_interrupt (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (noAdd : ∀ fiber, m.fiber? id = some fiber → NoAdd fiber.frame.stack)
    (held : Funded q m (.afterInterrupt id yielding kind :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.afterInterrupt id yielding kind) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · rename_i fiber found
    simp only [settle, List.nil_append, List.cons_append]
    apply update q m fiber
      {fiber with frame := {fiber.frame with current := (asVoidCode (interpOf root table)
        (awaitCode (interpOf root table) m kind))}}
      (.afterInterrupt id yielding kind :: rest) _ held unique
      (by simpa only [fiber_id_of_lookup found] using found) rfl
    simpa only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] using
      Nat.add_le_add_right (replace_code q fiber _ (noAdd fiber found)
        (await_void_zero root table q m kind)) ((rest.map (commandCredits q)).sum)

/-- A race-cancel command schedules only zero-credit administrative commands. -/
theorem race_cancel (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (race : Nat) (id : FiberId) (yielding : Bool) (remaining visited : List FiberId)
    (rest : List Command) (held : Funded q m (.raceCancel race id yielding remaining visited :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.raceCancel race id yielding remaining visited) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  cases remaining with
  | nil => exact held
  | cons target remaining =>
    simp only [driveStep]
    split
    · exact held
    · split
      · simpa only [Funded, List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] using held
      · exact held

/-- Clearing the exit bookkeeping can only discard saved release credit. -/
theorem cleared_debit (root : NativeEff) (table : RowTable) (q : List Nat) (fiber : Fiber) :
    fiberCredits q (fiber.cleared (interpOf root table)) ≤ fiberCredits q fiber := by
  change currentCredits q fiber.frame.current + 0 +
    (fiber.dispatcher.buckets.map fun bucket => (bucket.tasks.map (taskCredits q)).sum).sum ≤
    currentCredits q fiber.frame.current + stackCredits q fiber.frame.current fiber.frame.stack +
      (fiber.dispatcher.buckets.map fun bucket => (bucket.tasks.map (taskCredits q)).sum).sum
  omega

/-- Exit clearing discards credits only from the selected existing fiber. -/
theorem exit_done (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (rest : List Command) (unique : (m.fibers.map RunFiber.id).Nodup)
    (held : Funded q m (.exitDone id :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.exitDone id) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · rename_i fiber found
    apply update q m fiber (fiber.cleared (interpOf root table)) (.exitDone id :: rest) rest held unique
      (by simpa only [fiber_id_of_lookup found] using found) rfl
    simpa only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] using
      Nat.add_le_add_right (cleared_debit root table q fiber) ((rest.map (commandCredits q)).sum)

/-- Replacing only metadata retains the list of stored fiber identities. -/
theorem modify_ids (m : NativeMachine) (id : FiberId) (edit : Fiber → Fiber) :
    ((m.modify id edit).fibers.map RunFiber.id) = m.fibers.map RunFiber.id := by
  unfold RunMachine.modify
  split
  · rfl
  · exact RunMachine.update_keeps_ids _ _

/-- Parent tracking and child observers change no release credit. -/
theorem track_child (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (parent child : FiberId) (rest : List Command) (unique : (m.fibers.map RunFiber.id).Nodup)
    (held : Funded q m (.trackChild parent child :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.trackChild parent child) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · split
    · exact tail q m _ rest held
    · apply modify q _ child (fun f => {f with observers := f.observers ++ [.untrackChild parent]})
        rest _ _ (fun _ => rfl) (fun _ => Nat.le_refl _)
      · exact modify q m parent (fun f => {f with children := f.children ++ [child]})
          rest (tail q m _ rest held) unique (fun _ => rfl) (fun _ => Nat.le_refl _)
      · rw [modify_ids]
        exact unique

/-- The parallel close's administrative iterator carries no foreign finalizer credit. -/
theorem close_parallel (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (noAdd : ∀ fiber, m.fiber? id = some fiber → NoAdd fiber.frame.stack)
    (held : Funded q m (.closeParAwait id yielding fibers :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.closeParAwait id yielding fibers) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · rename_i fiber found
    simp only [settle, List.nil_append, List.cons_append]
    apply update q m fiber
      {fiber with frame := {fiber.frame with
        current := .suspend (.park (.awaitAll fibers))
        stack := .iterator (.store .closeParDone) .unit :: fiber.frame.stack}}
      (.closeParAwait id yielding fibers :: rest) _ held unique
      (by simpa only [fiber_id_of_lookup found] using found) rfl
    simp only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add]
    change currentCredits q (.suspend (.park (.awaitAll fibers))) +
      stackCredits q (.suspend (.park (.awaitAll fibers)))
        (.iterator (.store .closeParDone) .unit :: fiber.frame.stack) +
      (fiber.dispatcher.buckets.map fun bucket => (bucket.tasks.map (taskCredits q)).sum).sum + _ ≤ _
    simp only [currentCredits, stackCredits, futureCredits, Nat.zero_add, fiberCredits,
      noAdd_full q fiber.frame.current _ (noAdd fiber found)]
    omega

/-- Observer commands carry no queued answer credit. -/
theorem observer_commands (q : List Nat) (id : FiberId) (exit : ExitV) (observers : List Observer) :
    ((observers.map (.observe id exit)).map (commandCredits q)).sum = 0 := by
  induction observers with
  | nil => rfl
  | cons observer rest ih =>
    simpa only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] using ih

/-- Native exit publication and child cleanup retain the available registration credit. -/
theorem finish (root : NativeEff) (table : RowTable) (q : List Nat) (m : NativeMachine)
    (id : FiberId) (exit : ExitV) (rest : List Command)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (empty : ∀ fiber, m.fiber? id = some fiber → fiber.frame.stack = [])
    (held : Funded q m (.finish id exit :: rest)) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) m (.finish id exit) rest
    Funded q out.1 out.2 := by
  letI := evaluatorFor root table
  simp only [driveStep]
  split
  · exact tail q m _ rest held
  · rename_i fiber found
    have own : m.fiber? fiber.id = some fiber := by
      simpa only [fiber_id_of_lookup found] using found
    unfold exitFiber
    dsimp only
    split
    · simp only [exitFiber.exitInterruptChildren, List.cons_append, List.nil_append]
      apply emit q _ _ _ _ rfl rfl
      let next : Fiber := {fiber with
        finalizing := some exit
        running := false
        frame := {fiber.frame with
          deferredInterrupt := false
          current := .onSuccess ((interpOf root table).interruptAllCode fiber.children) (.restore exit)}}
      apply update q m fiber next (.finish id exit :: rest) _ held unique own rfl
      have noAdd : NoAdd fiber.frame.stack := by rw [empty fiber found]; exact noAdd_empty
      have debit := replace_code q fiber
        (.onSuccess ((interpOf root table).interruptAllCode fiber.children) (.restore exit)) noAdd rfl
      simpa only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add, next, fiberCredits] using
        Nat.add_le_add_right debit ((rest.map (commandCredits q)).sum)
    · let published : Fiber := ({fiber with running := false} : Fiber).publish exit
      let middle := (m.update published).emit [RunEvent.exited fiber.id exit]
      have pub : Funded q middle rest := by
        apply emit q _ _ _ _ rfl rfl
        apply update q m fiber published (.finish id exit :: rest) rest held unique own rfl
        simp only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add]
        exact Nat.le_refl _
      have middleUnique : (middle.fibers.map RunFiber.id).Nodup := by
        change ((m.update published).fibers.map RunFiber.id).Nodup
        have ids : (m.update published).fibers.map RunFiber.id = m.fibers.map RunFiber.id :=
          RunMachine.update_keeps_ids published m
        rw [ids]
        exact unique
      have pubFound : middle.fiber? published.id = some published :=
        fiber_lookup_update_self own published rfl
      change let out : NativeMachine × List Command := match published.observers with
        | [] => (middle.update (published.cleared (interpOf root table)), [.drainDue])
        | observers => (middle, observers.map (.observe published.id exit) ++ [.exitDone published.id, .drainDue])
        Funded q out.1 (out.2 ++ rest)
      split
      · simp only [List.cons_append, List.nil_append]
        apply update q middle published (published.cleared (interpOf root table)) rest (.drainDue :: rest)
          pub middleUnique pubFound rfl
        simpa only [List.map_cons, List.sum_cons, commandCredits, Nat.zero_add] using
          Nat.add_le_add_right (cleared_debit root table q published) ((rest.map (commandCredits q)).sum)
      · apply queue q middle rest _ pub
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, commandCredits, observer_commands, Nat.zero_add]
        exact Nat.le_refl _

end Effect4.Program.ReleaseCustody.CommandDebit
