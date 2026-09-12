import Effect4.Machine.Fibers

/-!
# Deep.Clauses

Owner: the mechanism clauses of the reference machine — one theorem per rc.112 arm,
cited by line as the census rows are, over the machine `src/Effect4/Machine/Fibers.lean` defines.

These are the witnesses the runtime census joins to (`Test/Audit/RuntimeCoverage.lean`)
for the fiber-side rows: the run-loop top, the per-entry budget and its one yield injection,
the scheduler's verdict, buckets, arming, drain and flush, the yield-now resume guard, the
interrupt entry (recorded always, applied only when idle and interruptible, deferred while
running, accumulating), the fork (mask by options, tracked unless daemon, fresh id, the
asymmetric start), join and await on an exited or a live target, the children snapshot and
the await of the new ones, the scope link of a running fiber, the runtime entries and the
`AsyncFiberError` defect. Each is an equation on the machine's own definition, so a clause
is what the machine *does*, never a restatement beside it.

Every statement fixes the shape it speaks about by construction — a fiber whose current
primitive is the arm's, a machine whose fiber table holds the target — so the proofs are
the definitions computing, and the census reads the clause off the machine.
-/

-- The `DecidableEq` section variables are what the machine's definitions take; a clause
-- about a definition that does not need them is stated in the same section anyway.
set_option linter.unusedSectionVars false

namespace Effect4.Machine

universe u v

open Effect4

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-! ## The run-loop top and the per-entry budget -/

/-- A deferred interrupt is cleared at the top of the iteration and the current primitive
becomes the pending cause's failure (`:639-642`). census: checkpoint.runloop-top -/
theorem runloopTop_deferred (f : RunFiber ν σ β ε δ ι α χ) (h : f.frame.deferredInterrupt = true) :
    runloopTop f =
      { f with frame :=
          { f.frame with deferredInterrupt := false, current := Prim.failure f.frame.pendingCause } } := by
  simp [runloopTop, h]

/-- With no deferred interrupt the top of the loop changes nothing (`:639`).
census: checkpoint.runloop-top -/
theorem runloopTop_idle (f : RunFiber ν σ β ε δ ι α χ) (h : f.frame.deferredInterrupt = false) :
    runloopTop f = f := by
  simp [runloopTop, h]

/-- After the top of the loop no interrupt is deferred. census: checkpoint.runloop-top -/
theorem runloopTop_clears (f : RunFiber ν σ β ε δ ι α χ) :
    (runloopTop f).frame.deferredInterrupt = false := by
  unfold runloopTop
  split <;> simp_all

/-- The op counter counts every iteration (`:643`). census: rule.budget-per-runloop-entry -/
theorem countOp_count (f : RunFiber ν σ β ε δ ι α χ) :
    (countOp f).currentOpCount = f.currentOpCount + 1 := rfl

/-- The counter resets on every `evaluate` entry (`:599-628`, `:634`): the fiber the loop
starts from counts from zero. census: rule.budget-per-runloop-entry -/
theorem drive_evaluate_enters (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (hexit : f.exit = none) (hrun : f.running = false) (hpark : f.parked = Parked.notParked) :
    drive interp (fuel + 1) m (Cmd.evaluate id :: rest) =
      drive interp fuel
        ((m.update { f with running := true, currentOpCount := 0, parked := Parked.notParked }).emit
          [RunEvent.started id])
        (Cmd.loop id false :: rest) := by
  simp [drive, driveState, driveStep, hs, hf, hexit, hrun, hpark]

/-- `evaluate` on a fiber that has exited is a no-op (`:600`).
census: rule.budget-per-runloop-entry -/
theorem drive_evaluate_exited (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (hexit : f.exit.isSome = true) :
    drive interp (fuel + 1) m (Cmd.evaluate id :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hf, hexit]

/-- `evaluate` on a running fiber is a no-op (`:601`). census: rule.budget-per-runloop-entry -/
theorem drive_evaluate_running (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (hrun : f.running = true) :
    drive interp (fuel + 1) m (Cmd.evaluate id :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hf, hrun]

/-- The scheduler's verdict by default: the op count has reached the budget
(`Scheduler.ts:174-176`). census: scheduler.should-yield -/
theorem yieldVerdict_default (f : RunFiber ν σ β ε δ ι α χ) (h : f.yieldOverride = none) :
    yieldVerdict f = decide (f.currentOpCount >= f.maxOpsBeforeYield) := by
  simp [yieldVerdict, h]

/-- The tape's override answers instead (`Scheduler.ts:78-81`). census: scheduler.should-yield -/
theorem yieldVerdict_override (f : RunFiber ν σ β ε δ ι α χ) (verdict : Bool)
    (h : f.yieldOverride = some verdict) : yieldVerdict f = verdict := by
  simp [yieldVerdict, h]

/-- The latch: once a yield has been injected in this entry, no second one is (`:648`).
census: rule.budget-per-runloop-entry -/
theorem injectYield_latched (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) :
    injectYield m f true = none := by
  simp [injectYield]

/-- `PreventSchedulerYield` bypasses the check (`:645`, `Scheduler.ts:295-298`).
census: scheduler.prevent-yield-default -/
theorem injectYield_prevented (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (h : f.preventYield = true) : injectYield m f yielding = none := by
  simp [injectYield, h]

/-- No verdict, no injection (`:646`). census: scheduler.should-yield -/
theorem injectYield_no_verdict (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (h : yieldVerdict f = false) : injectYield m f yielding = none := by
  simp [injectYield, h]

/-- The injection (`:647-652`): save the current program in the ordinary
success-continuation stack protocol, set the latch and consume the override.
No guard or dispatcher task is allocated until the following Yield operation.
census: rule.budget-per-runloop-entry -/
theorem injectYield_fires (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (hp : f.preventYield = false) (hv : yieldVerdict f = true) :
    ∃ it : Iter ν σ β ε δ ι α χ St, injectYield m f false = some it ∧
      it.yielding = true ∧ it.outcome = Outcome.continue_ ∧
      it.fiber.frame.current = Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current ∧
      it.fiber.yieldOverride = none ∧
      it.fiber.dispatcher = f.dispatcher ∧
      it.machine.nextToken = m.nextToken := by
  refine ⟨⟨m.emit [RunEvent.yieldInjected f.id f.currentOpCount],
    ({ f with
        yieldOverride := none
        frame := { f.frame with current := Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current } }),
    true, Outcome.continue_, []⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [injectYield, hp, hv]

/-- The injected wrapper is evaluated in the already counted iteration
(`:638-655`). census: rule.budget-per-runloop-entry -/
theorem iteration_injected (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (it : Iter ν σ β ε δ ι α χ St) (h : injectYield m (countOp (runloopTop f)) yielding = some it) :
    iteration interp m f yielding = evaluatePrim interp it.machine it.fiber it.yielding := by
  simp [iteration, h]

/-- … and the evaluation of the current primitive otherwise (`:655`).
census: rule.budget-per-runloop-entry -/
theorem iteration_evaluates (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (h : injectYield m (countOp (runloopTop f)) yielding = none) :
    iteration interp m f yielding = evaluatePrim interp m (countOp (runloopTop f)) yielding := by
  simp [iteration, h]

/-! ## The dispatcher: buckets, arming, drain, flush -/

/-- A task joins its priority's bucket at the end (`Scheduler.ts:105-131`, FIFO).
census: scheduler.priority-buckets -/
theorem Dispatcher.enqueue_same_bucket (d : Dispatcher ν σ β ε δ ι α) (priority : Nat)
    (task : Task ν σ β ε δ ι α) (bucket : Bucket ν σ β ε δ ι α) (rest : List (Bucket ν σ β ε δ ι α))
    (hb : d.buckets = bucket :: rest) (hp : bucket.priority = priority) :
    (d.enqueue priority task).buckets = ⟨bucket.priority, bucket.tasks ++ [task]⟩ :: rest := by
  simp [Dispatcher.enqueue, Dispatcher.insert, hb, hp]

/-- A lower priority opens a bucket in front (`Scheduler.ts:105-131`, ascending).
census: scheduler.priority-buckets -/
theorem Dispatcher.enqueue_lower_priority (d : Dispatcher ν σ β ε δ ι α) (priority : Nat)
    (task : Task ν σ β ε δ ι α) (bucket : Bucket ν σ β ε δ ι α) (rest : List (Bucket ν σ β ε δ ι α))
    (hb : d.buckets = bucket :: rest) (hne : bucket.priority ≠ priority) (hlt : priority < bucket.priority) :
    (d.enqueue priority task).buckets = ⟨priority, [task]⟩ :: bucket :: rest := by
  simp [Dispatcher.enqueue, Dispatcher.insert, hb, hne, hlt]

/-- An empty dispatcher takes the task as its one bucket. census: scheduler.priority-buckets -/
theorem Dispatcher.enqueue_empty (priority : Nat) (task : Task ν σ β ε δ ι α) :
    ((Dispatcher.empty : Dispatcher ν σ β ε δ ι α).enqueue priority task).buckets = [⟨priority, [task]⟩] := rfl

/-- Enqueueing arms the dispatcher (`Scheduler.ts:207-212`); an already armed one stays
armed, which is the "later tasks join the armed callback" clause.
census: scheduler.dispatcher-arming -/
theorem Dispatcher.enqueue_arms (d : Dispatcher ν σ β ε δ ι α) (priority : Nat)
    (task : Task ν σ β ε δ ι α) : (d.enqueue priority task).armed = true := rfl

/-- `runTasks` takes the whole snapshot once, in bucket order, and leaves an idle
dispatcher (`Scheduler.ts:225-233`). census: scheduler.run-tasks-drain-once -/
theorem Dispatcher.drain_eq (d : Dispatcher ν σ β ε δ ι α) :
    d.drain = ((d.buckets.map Bucket.tasks).flatten, Dispatcher.empty) := rfl

/-- A drained dispatcher is disarmed: a task enqueued during the run re-arms it and waits
for the next host task. census: scheduler.run-tasks-drain-once -/
theorem Dispatcher.drain_disarms (d : Dispatcher ν σ β ε δ ι α) : (d.drain).2.armed = false := rfl

/-- A `fire` on an unknown owner does nothing. census: scheduler.host-loop -/
theorem fire_unknown (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (h : m.fiber? owner = none) :
    stepDecision.fire interp fuel m owner = m := by
  unfold stepDecision.fire fireState
  rw [h]

/-- The host's callback (`Scheduler.ts:214-217`, the tape's `fire`): the owner's dispatcher
is no longer scheduled, it is drained once, and the snapshot runs in order, a start as an
`evaluate` and a resume as a `resume`, each followed by the store's due resumes.
census: scheduler.host-loop -/
theorem fire_eq (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (o : RunFiber ν σ β ε δ ι α χ)
    (h : m.fiber? owner = some o) :
    stepDecision.fire interp fuel m owner =
      ((o.dispatcher.drain).1.foldl (fireStep interp fuel owner)
        ((m.update { o with dispatcher := (o.dispatcher.drain).2 }).disarm owner, true)).1 := by
  unfold stepDecision.fire fireState
  rw [h]

/-- The first task scheduled on a dispatcher arms it: a host callback is scheduled behind
those already scheduled (`Scheduler.ts:207-212`, R2-15). census: scheduler.dispatcher-arming -/
theorem RunMachine.arm_new (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (h : m.armed.contains owner = false) : (m.arm owner).armed = m.armed ++ [owner] := by
  unfold RunMachine.arm
  rw [h]
  simp

/-- A later task joins the armed callback: the order is unchanged.
census: scheduler.dispatcher-arming -/
theorem RunMachine.arm_known (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (h : m.armed.contains owner = true) : (m.arm owner).armed = m.armed := by
  unfold RunMachine.arm
  rw [h]
  simp

/-- Arming changes nothing but the schedule. census: scheduler.dispatcher-arming -/
theorem RunMachine.arm_fields (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    (m.arm owner).fibers = m.fibers ∧ (m.arm owner).nextToken = m.nextToken ∧
      (m.arm owner).trace = m.trace ∧ (m.arm owner).state = m.state := ⟨rfl, rfl, rfl, rfl⟩

/-- A callback that ran is no longer scheduled. census: scheduler.host-loop -/
theorem RunMachine.disarm_eq (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    (m.disarm owner).armed = m.armed.filter fun x => x ≠ owner := rfl

/-- The event loop with nothing scheduled runs nothing. census: scheduler.flush -/
theorem flushAll_idle (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (h : m.armed = []) :
    stepDecision.flushAll interp fuel (rounds + 1) m = m := by
  simp [stepDecision.flushAll, flushAllState, h]

/-- The event loop runs the scheduled callbacks in arming order, one per round: the head of
the schedule fires, and the loop goes round on what it left (`setImmediate` FIFO,
`Scheduler.ts:207-212`; R2-15 — fiber order was an assumption, recorded, and wrong).
census: scheduler.flush -/
theorem flushAll_round (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (rest : List FiberId)
    (h : m.armed = owner :: rest) (hs : m.stuck = none)
    (hf : (fireState interp fuel m owner).2 = true) :
    stepDecision.flushAll interp fuel (rounds + 1) m =
      stepDecision.flushAll interp fuel rounds (stepDecision.fire interp fuel m owner) := by
  simp [stepDecision.flushAll, flushAllState, stepDecision.fire, h, hs, hf]

/-- `MixedSchedulerDispatcher.flush` (`Scheduler.ts:238-246`) on a dispatcher holding no
task runs nothing. census: entry.run-sync-exit-with -/
theorem flushRoot_idle (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (root : FiberId) (m : RunMachine ν σ β ε δ ι α χ St) (o : RunFiber ν σ β ε δ ι α χ)
    (h : m.fiber? root = some o) (hb : o.dispatcher.buckets = []) :
    stepDecision.flushRoot interp fuel root (rounds + 1) m = m := by
  simp [stepDecision.flushRoot, flushRootState, h, hb]

/-- … and while it holds tasks its callback is cancelled and they run, round after round.
census: entry.run-sync-exit-with -/
theorem flushRoot_round (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (root : FiberId) (m : RunMachine ν σ β ε δ ι α χ St) (o : RunFiber ν σ β ε δ ι α χ)
    (h : m.fiber? root = some o) (hb : o.dispatcher.buckets.isEmpty = false)
    (hs : m.stuck = none) (hf : (fireState interp fuel m root).2 = true) :
    stepDecision.flushRoot interp fuel root (rounds + 1) m =
      stepDecision.flushRoot interp fuel root rounds (stepDecision.fire interp fuel m root) := by
  simp [stepDecision.flushRoot, flushRootState, stepDecision.fire, h, hb, hs, hf]

/-! The two budget references default to `2048` and `false` (`Scheduler.ts:269-272`,
`:295-298`); the machine reads them through `RunInterp.budgetOf`, and the defaults are
`Effect4.Machine.Env.hooks_empty` (`src/Effect4/Machine/Context.lean`). -/

/-! ## Yield now, and the resume guard -/

/-- `yieldNowWith` (`:982-990`): the fiber parks behind a fresh guard, its resume queued at
the given priority with `exitVoid`, and its current primitive is already the void success.
census: scheduler.yield-now-resume-guard -/
theorem evaluatePrim_yieldNowWith (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (priority : Nat) :
    let g : RunFiber ν σ β ε δ ι α χ :=
      { f with frame := { f.frame with current := Prim.yieldNowWith priority } }
    let it := evaluatePrim interp m g yielding
    it.outcome = Outcome.parked ∧
      it.fiber.parked = Parked.withGuard m.nextToken ∧
      it.fiber.frame.current = Prim.success interp.voidValue ∧
      it.fiber.dispatcher =
        f.dispatcher.enqueue priority (Task.resume f.id m.nextToken (Prim.success interp.voidValue)) ∧
      it.machine.nextToken = m.nextToken + 1 ∧
      it.nested = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Yield` is overloaded (`:656-668`): where rc.112 reads `_yielded` as an exit the fiber is
finished, and where it reads a thunk the fiber is parked; the machine's loop takes the two
outcomes apart. census: rule.yield-is-overloaded -/
theorem drive_loop_parked (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.parked)
    (hd : (iteration interp m f yielding).fiber.frame.deferredInterrupt = false) :
    drive interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      drive interp fuel
        ((iteration interp m f yielding).machine.update
          { (iteration interp m f yielding).fiber with running := false })
        ((iteration interp m f yielding).nested ++ rest) := by
  simp [drive, driveState, driveStep, settle, hs, hf, h, hd]

/-- … and a `Yield` returned while the nested work of the same iteration recorded a deferred
interrupt clears the guard and goes round again in the same entry (`:662-667`, D6a): the next
loop top turns the deferred interrupt into the failure. census: rule.yield-is-overloaded -/
theorem drive_loop_parked_deferred (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.parked)
    (hd : (iteration interp m f yielding).fiber.frame.deferredInterrupt = true) :
    drive interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      drive interp fuel
        ((iteration interp m f yielding).machine.update
          { (iteration interp m f yielding).fiber with parked := Parked.notParked, pending := [] })
        ((iteration interp m f yielding).nested ++
          [Cmd.loop id (iteration interp m f yielding).yielding] ++ rest) := by
  simp [drive, driveState, driveStep, settle, hs, hf, h, hd]

/-- … and where the iteration continues, the loop goes on with the latch it answered
(`:648`, `:667`). census: rule.yield-is-overloaded -/
theorem drive_loop_continues (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.continue_) :
    drive interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      drive interp fuel
        ((iteration interp m f yielding).machine.update (iteration interp m f yielding).fiber)
        ((iteration interp m f yielding).nested ++
          [Cmd.loop id (iteration interp m f yielding).yielding] ++ rest) := by
  simp [drive, driveState, driveStep, settle, hs, hf, h]

/-- `Sync[evaluate]` (`:931-935`): the thunk runs against the store first, its value becomes
the fiber's `current`, the resumes it owes are the nested `drainDue`, and the pop is owed
*after* them (R2-1). census: op.Sync -/
theorem evaluatePrim_sync_answers (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (state : St) (value : β)
    (hpark : interp.parkOf (Prim.sync thunk) = none)
    (hsync : interp.syncState thunk m.state = some (state, value)) :
    let g : RunFiber ν σ β ε δ ι α χ := { f with frame := { f.frame with current := Prim.sync thunk } }
    evaluatePrim interp m g yielding =
      ⟨{ m with state := state }, { g with frame := { g.frame with current := Prim.success value } },
        yielding, Outcome.answered, [Cmd.drainDue]⟩ := by
  simp only [evaluatePrim, hpark, hsync]

/-- A `sync` the store does not recognise answers the interp's pure `syncValue` and owes
nothing; the pop is still deferred to `Cmd.deliver`, so an `OnExit` frame under it meets its
finalizer program. census: op.Sync -/
theorem evaluatePrim_sync_pure (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (hpark : interp.parkOf (Prim.sync thunk) = none)
    (hsync : interp.syncState thunk m.state = none) :
    let g : RunFiber ν σ β ε δ ι α χ := { f with frame := { f.frame with current := Prim.sync thunk } }
    evaluatePrim interp m g yielding =
      ⟨m, { g with frame := { g.frame with current := Prim.success (interp.syncValue thunk) } },
        yielding, Outcome.answered, []⟩ := by
  simp only [evaluatePrim, hpark, hsync]

/-- An answered iteration: the nested commands run first, then the delivery (`:932-933`).
census: op.Sync -/
theorem settle_answered (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α))
    (it : Iter ν σ β ε δ ι α χ St) (h : it.outcome = Outcome.answered) :
    settle id rest it =
      (it.machine.update it.fiber, it.nested ++ [Cmd.deliver id it.yielding] ++ rest) := by
  simp [settle, h]

/-- A finished iteration: the nested commands run first, then the exit path (`:611-628`, M1).
census: rule.children-interrupted-after-exit -/
theorem settle_finished (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α))
    (it : Iter ν σ β ε δ ι α χ St) (exit : Exit β ε δ ι α)
    (h : it.outcome = Outcome.finished exit) :
    settle id rest it =
      (it.machine.update it.fiber, it.nested ++ [Cmd.finish id exit] ++ rest) := by
  simp [settle, h]

/-- The loop on an answered iteration (R2-1). census: op.Sync -/
theorem drive_loop_answered (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.answered) :
    drive interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      drive interp fuel
        ((iteration interp m f yielding).machine.update (iteration interp m f yielding).fiber)
        ((iteration interp m f yielding).nested ++
          [Cmd.deliver id (iteration interp m f yielding).yielding] ++ rest) := by
  simp [drive, driveState, driveStep, settle, hs, hf, h]

/-- The delivery (`:933-934`): the answer is evaluated as the fiber's `current` — no loop
top, no op count — so its `getCont` sees what the nested commands recorded, and an `OnExit`
frame's finalizer program runs through `finalizerOr`. census: op.Sync -/
theorem drive_deliver (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f) :
    drive interp (fuel + 1) m (Cmd.deliver id yielding :: rest) =
      drive interp fuel (settle id rest (evaluatePrim interp m f yielding)).1
        (settle id rest (evaluatePrim interp m f yielding)).2 := by
  simp [drive, driveState, driveStep, hs, hf]

/-- The exit path as a command (`:611-628`): the fiber is re-read, its loop is over, and the
commands `exitFiber` owes — the counted re-entry, or the observers, the clearing and the
drain of the store's owed resumes — precede the rest. census: fork.child -/
theorem drive_finish (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (exit : Exit β ε δ ι α)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f) :
    drive interp (fuel + 1) m (Cmd.finish id exit :: rest) =
      (let r := exitFiber interp m { f with running := false } exit
       drive interp fuel r.1 (r.2 ++ rest)) := by
  simp [drive, driveState, driveStep, hs, hf]

/-- `forkUnsafe`'s tracking (`:5279-5282`, D6b), after the child's immediate run or its
scheduling: a child still live joins the parent's children and gets the untrack observer.
census: rule.only-fork-child-tracks -/
theorem drive_trackChild_live (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent child : FiberId) (c : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hc : m.fiber? child = some c)
    (hx : c.exit = none) :
    drive interp (fuel + 1) m (Cmd.trackChild parent child :: rest) =
      drive interp fuel
        ((m.modify parent fun p => { p with children := p.children ++ [child] }).modify child
          fun c => { c with observers := c.observers ++ [Observer.untrackChild parent] })
        rest := by
  simp [drive, driveState, driveStep, hs, hc, hx]

/-- A child that exited during its immediate run is never tracked (`:5279`).
census: rule.only-fork-child-tracks -/
theorem drive_trackChild_exited (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent child : FiberId) (c : RunFiber ν σ β ε δ ι α χ)
    (exit : Exit β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none)
    (hc : m.fiber? child = some c) (hx : c.exit = some exit) :
    drive interp (fuel + 1) m (Cmd.trackChild parent child :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hc, hx]

/-- The resume guard (`:990-993`, `:1121`): a resume whose token is not the guard the fiber
is parked behind is dropped. census: scheduler.yield-now-resume-guard -/
theorem drive_resume_wrong_token (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (token guard : Nat)
    (answer : Prim ν σ β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (ht : m.fiber? id = some t) (hp : t.parked = Parked.withGuard guard)
    (hne : guard ≠ token) :
    drive interp (fuel + 1) m (Cmd.resume id token answer :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, ht, hp, hne]

/-- A resume on the right guard unparks the fiber, drops the pending entry, installs the
answer and evaluates (`:1121-1126`). census: scheduler.yield-now-resume-guard -/
theorem drive_resume_guard (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (token : Nat)
    (answer : Prim ν σ β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (ht : m.fiber? id = some t) (hp : t.parked = Parked.withGuard token) :
    drive interp (fuel + 1) m (Cmd.resume id token answer :: rest) =
      drive interp fuel
        ((m.update { t with
            parked := Parked.notParked
            pending := t.pending.filter fun p => p.token ≠ token
            frame := { t.frame with current := answer } }).emit [RunEvent.resumedWith id token answer])
        (Cmd.evaluate id :: rest) := by
  simp [drive, driveState, driveStep, hs, ht, hp]

/-- A resume on a fiber that is not parked is dropped. census: scheduler.yield-now-resume-guard -/
theorem drive_resume_not_parked (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (token : Nat)
    (answer : Prim ν σ β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (ht : m.fiber? id = some t) (hp : t.parked = Parked.notParked) :
    drive interp (fuel + 1) m (Cmd.resume id token answer :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, ht, hp]

/-! ## The interrupt entry -/

/-- After the exit exists an interrupt is a no-op (`:575-577`). census: interrupt.unsafe-entry -/
theorem interruptRecord_exited (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (h : f.exit.isSome = true) : interruptRecord interp interruptor extra f = (f, false) := by
  simp [interruptRecord, h]

/-- The cause an interrupt records: the interruptor's, annotated by the target's stack frame
and the caller's annotations, combined with what was already recorded (`:578-587`).
-/
def interruptCauseOf (interp : RunInterp ν σ β ε δ ι α χ St) (interruptor : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) : Cause ε δ ι α :=
  let cause := Cause.annotate
    (Supervision.interruptCause interp.encodeFiber interruptor (interp.stackAnnotations f.id)) extra false
  match f.frame.interruptedCause with
  | none => cause
  | some previous => Cause.combine previous cause

/-- Before the exit, the interrupt is always recorded (`:578-587`): the target's frame carries
the cause afterwards, whatever else happens. census: rule.record-and-apply-separate -/
theorem interruptRecord_records (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (h : f.exit = none) :
    (interruptRecord interp interruptor extra f).1.frame.interruptedCause =
      some (interruptCauseOf interp interruptor extra f) := by
  unfold interruptRecord interruptCauseOf
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
  simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  cases f.frame.interruptedCause <;> simp only <;> split <;> (try split) <;> rfl

/-- Successive interruptors accumulate by `causeCombine` (`:585-587`).
census: interrupt.accumulate -/
theorem interruptRecord_accumulates (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (previous : Cause ε δ ι α) (h : f.exit = none) (hprev : f.frame.interruptedCause = some previous) :
    (interruptRecord interp interruptor extra f).1.frame.interruptedCause =
      some (Cause.combine previous
        (Cause.annotate
          (Supervision.interruptCause interp.encodeFiber interruptor (interp.stackAnnotations f.id))
          extra false)) := by
  rw [interruptRecord_records interp interruptor extra f h]
  simp [interruptCauseOf, hprev]

/-- Interruptible and running: the interrupt is deferred to the next loop top and not applied
now (`:588-590`). census: rule.record-and-apply-separate -/
theorem interruptRecord_running_defers (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (h : f.exit = none) (hi : f.frame.interruptible = true) (hr : f.running = true) :
    (interruptRecord interp interruptor extra f).2 = false ∧
      (interruptRecord interp interruptor extra f).1.frame.deferredInterrupt = true := by
  unfold interruptRecord
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
  simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  cases f.frame.interruptedCause <;> simp [hi, hr]

/-- Interruptible and idle: the interrupt is applied now — the fiber is unparked, its pending
parks dropped, and its current primitive is the accumulated cause's failure (`:591-594`).
census: rule.record-and-apply-separate -/
theorem interruptRecord_idle_applies (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (h : f.exit = none) (hi : f.frame.interruptible = true) (hr : f.running = false) :
    (interruptRecord interp interruptor extra f).2 = true ∧
      (interruptRecord interp interruptor extra f).1.parked = Parked.notParked ∧
      (interruptRecord interp interruptor extra f).1.pending = [] ∧
      (interruptRecord interp interruptor extra f).1.frame.current =
        Prim.failure (interruptCauseOf interp interruptor extra f) := by
  unfold interruptRecord interruptCauseOf
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
  simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  cases f.frame.interruptedCause <;> simp [hi, hr]

/-- Masked: recorded, never applied (`:588`, the `else` of `:595`).
census: rule.record-and-apply-separate -/
theorem interruptRecord_masked (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (h : f.exit = none) (hi : f.frame.interruptible = false) :
    (interruptRecord interp interruptor extra f).2 = false ∧
      (interruptRecord interp interruptor extra f).1.frame.deferredInterrupt =
        f.frame.deferredInterrupt ∧
      (interruptRecord interp interruptor extra f).1.frame.current = f.frame.current := by
  unfold interruptRecord
  dsimp only [FiberCore.interruptedCause, FiberCore.recordCause, FiberCore.interruptible,
    FiberCore.answerWith, FiberCore.failure, FiberCore.setDeferred, frameCore]
  simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  cases f.frame.interruptedCause <;> simp [hi]

/-- A parked fiber holding a deferred interrupt fires its park's cancel on the way out
(`:656-668`): the interrupt applies now because the fiber is idle, and the failure it installs
meets the `AsyncFinalizer` frame the park pushed, whose `contE` runs the cancel
(`Effect4.FrameFiber.armE_asyncFinalizer_interrupt`). census: checkpoint.post-yield-cancel -/
theorem interruptRecord_parked_applies (interp : RunInterp ν σ β ε δ ι α χ St)
    (interruptor : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ)
    (h : f.exit = none) (hi : f.frame.interruptible = true) (hr : f.running = false) :
    (interruptRecord interp interruptor extra f).2 = true ∧
      (interruptRecord interp interruptor extra f).1.parked = Parked.notParked ∧
      (interruptRecord interp interruptor extra f).1.pending = [] := by
  have := interruptRecord_idle_applies interp interruptor extra f h hi hr
  exact ⟨this.1, this.2.1, this.2.2.1⟩

/-! ## Fork -/

/-- The child `forkUnsafe` constructs (`:5264-5284`), as `spawn` builds it: the next id, the
parent's context and budget, the mask by the options, and the untrack observer unless daemon. -/
def spawnChild (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) : RunFiber ν σ β ε δ ι α χ :=
  let childInterruptible :=
    match options.maskMode with
    | Supervision.MaskMode.interruptible => true
    | Supervision.MaskMode.uninterruptible => false
    | Supervision.MaskMode.inherit => parent.frame.interruptible
  RunFiber.make ⟨m.nextId⟩ program childInterruptible (interp.budgetOf parent.context) parent.context

/-- `forkUnsafe` (`:5264-5284`, D6b): the child takes the next id and is appended to the
machine, the id counter advances, and the parent is untouched — tracking is `Cmd.trackChild`
after the child's immediate run or its scheduling (`:5279-5282`). census: fork.unsafe -/
theorem spawn_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) :
    spawn interp m parent program options =
      ({ m with fibers := m.fibers ++ [spawnChild interp m parent program options], nextId := m.nextId + 1 }.emit
          [RunEvent.forked parent.id ⟨m.nextId⟩ options.daemon],
        parent, ⟨m.nextId⟩) := rfl

/-- The child's identity, context and mask (`:5264-5284`); it carries no observer yet.
census: fork.unsafe -/
theorem spawnChild_fields (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) :
    (spawnChild interp m parent program options).id = ⟨m.nextId⟩ ∧
      (spawnChild interp m parent program options).context = parent.context ∧
      (spawnChild interp m parent program options).frame.interruptible =
        (match options.maskMode with
          | Supervision.MaskMode.interruptible => true
          | Supervision.MaskMode.uninterruptible => false
          | Supervision.MaskMode.inherit => parent.frame.interruptible) ∧
      (spawnChild interp m parent program options).observers = [] := by
  cases hm : options.maskMode <;> simp [spawnChild, RunFiber.make, hm]

/-- No fork joins the parent's children at its spawn (`:5279-5282`, D6b): the tracking is a
command after the child's run, and only a non-daemon fork issues it (`withFiber_fork`).
census: rule.only-fork-child-tracks -/
theorem spawn_untracked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) :
    (spawn interp m parent program options).2.1 = parent := rfl

/-- The start is asymmetric (`:5274-5278`): immediately means on the caller's stack, as a
command; deferred means a start task at priority 0 on the parent's dispatcher.
census: rule.start-is-asymmetric -/
theorem start_eq (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (child : FiberId) :
    start m parent child true = (m, parent, [Cmd.evaluate child]) ∧
      start m parent child false =
        ((m.arm parent.id).emit [RunEvent.scheduledTask parent.id 0 (Task.start child)],
          { parent with dispatcher := parent.dispatcher.enqueue 0 (Task.start child) }, []) :=
  ⟨rfl, rfl⟩

/-- The root runs synchronously on the caller's stack (`runForkWith`, `:5410-5430`): a fresh
fiber over the caller context, evaluated at once, then the store's due resumes.
census: entry.run-fork-with -/
theorem runFork_eq (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ) :
    runFork interp fuel m program context =
      (drive interp fuel
        { m with
          fibers := m.fibers ++ [RunFiber.make ⟨m.nextId⟩ program true (interp.budgetOf context) context]
          nextId := m.nextId + 1 }
        [Cmd.evaluate ⟨m.nextId⟩, Cmd.drainDue], ⟨m.nextId⟩) := rfl

/-! ## Join and await -/

/-- A join or await on a target that has exited answers at once with the stored exit, as a
value for `await` and as an effect for `join` (`:561-562`, `:5291`, `:5304`).
census: fork.join -/
theorem evaluatePrim_join_done (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (target : FiberId) (mode : Supervision.ObserverMode)
    (t : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (hpark : interp.parkOf (Prim.sync thunk) = some (Except.ok (ParkKind.join target mode)))
    (ht : m.fiber? target = some t) (hexit : t.exit = some exit) :
    let g : RunFiber ν σ β ε δ ι α χ := { f with frame := { f.frame with current := Prim.sync thunk } }
    evaluatePrim interp m g yielding =
      ⟨m, { g with frame := { g.frame with current := interp.exitValue exit mode } }, yielding,
        Outcome.continue_, []⟩ := by
  simp only [evaluatePrim, hpark, ht, hexit]

/-- A join or await on a live target registers an observer on it, pushes the park's cleanup
as an `AsyncFinalizer` frame (the `callback`'s `sync(self.addObserver(…))` return, `:773`,
`:821`, `:1128-1141`; R2-3) and parks behind a fresh guard (`:5291`, `:5304`, `:565`).
census: fork.await -/
theorem evaluatePrim_join_live (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (target : FiberId) (mode : Supervision.ObserverMode)
    (t : RunFiber ν σ β ε δ ι α χ)
    (hpark : interp.parkOf (Prim.sync thunk) = some (Except.ok (ParkKind.join target mode)))
    (ht : m.fiber? target = some t) (hlive : t.exit = none) :
    let g : RunFiber ν σ β ε δ ι α χ := { f with frame := { f.frame with current := Prim.sync thunk } }
    evaluatePrim interp m g yielding =
      ⟨({ m with nextToken := m.nextToken + 1 }.update
          { t with observers := t.observers ++ [Observer.resumeAwait g.id m.nextToken mode] }).emit
          [RunEvent.parkedOn g.id m.nextToken],
        ({ g with frame := { g.frame with
            stack := Prim.asyncFinalizer (interp.cancelName interp.parkCancelName g.id m.nextToken) :: g.frame.stack } }).park
          ⟨m.nextToken, some target, [], [], Resume.void, false⟩, yielding, Outcome.parked, []⟩ := by
  simp only [evaluatePrim, hpark, ht, hlive]
  try rfl

/-- A join on a handle the machine does not hold is a stuck state, made observable
(S3 §5.1). census: fork.join -/
theorem evaluatePrim_join_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (target : FiberId) (mode : Supervision.ObserverMode)
    (hpark : interp.parkOf (Prim.sync thunk) = some (Except.ok (ParkKind.join target mode)))
    (ht : m.fiber? target = none) :
    let g : RunFiber ν σ β ε δ ι α χ := { f with frame := { f.frame with current := Prim.sync thunk } }
    (evaluatePrim interp m g yielding).outcome = Outcome.stuck (Stuck.unknownFiber target) := by
  simp [evaluatePrim, hpark, ht]

/-! ## Children -/

/-- `awaitAllChildren`'s snapshot (`:5318`): the parent's tracked children as a value.
census: fork.await-all-children -/
theorem withFiber_snapshotChildren (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) :
    evaluatePrim.withFiber interp m f yielding WithFiberAction.snapshotChildren =
      ⟨m, { f with frame := { f.frame with current := Prim.success (interp.fibersValue f.children) } },
        yielding, Outcome.continue_, []⟩ := rfl

/-- The exit half (`:5322-5331`): only the children added since the snapshot are awaited.
census: fork.await-all-children -/
theorem withFiber_awaitNewChildren (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (snapshot : List FiberId) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.awaitNewChildren snapshot) =
      (let r := countdownPark interp m f (f.children.filter fun c => !(snapshot.contains c)) Resume.void
       ⟨r.1, r.2.1, yielding,
        (match r.1.stuck with
          | some why => Outcome.stuck why
          | none => if r.2.2 then Outcome.parked else Outcome.continue_), []⟩) := rfl

/-- `fiberRunIn` (`:5447-5461`): an existing fiber is linked to a scope as a run-in with no
caller annotations, and the caller answers void. census: fork.fiber-run-in -/
theorem withFiber_runIn (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) (scope : Nat) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.runIn target scope) =
      (let r := linkScope interp m Supervision.ScopeMode.fiberRunIn scope target (some target)
        ReasonAnnotations.empty
       ⟨r.1, { f with frame := { f.frame with current := Prim.success interp.voidValue } }, yielding,
        (match r.1.stuck with
          | some why => Outcome.stuck why
          | none => Outcome.continue_), r.2⟩) := rfl

/-- Linking to a closed scope interrupts the fiber at once (`:5374`, `:5454`).
census: fork.fiber-run-in -/
theorem linkScope_closed (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (exit : Exit β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ)
    (hclosed : interp.scopeStatus scope m.state = some (some exit)) (ht : m.fiber? target = some t) :
    linkScope interp m mode scope target interruptor extra =
      (let r := interruptRecord interp interruptor extra t
       ((m.update r.1).emit [RunEvent.scopeClosedOnLink scope target,
          RunEvent.interruptRecorded interruptor target],
        if r.2 then [Cmd.evaluate target] else [])) := by
  simp [linkScope, hclosed, ht]

/-- An unknown scope halts the machine (M7). census: fork.fiber-run-in -/
theorem linkScope_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (h : interp.scopeStatus scope m.state = none) :
    linkScope interp m mode scope target interruptor extra = (m.halt (Stuck.unknownScope scope), []) := by
  simp [linkScope, h]

/-! ## The runtime entries -/

/-- `runCallbackWith` (`:5470-5490`): the root carries the exit observer under `key`.
census: entry.run-callback-with -/
theorem runCallback_eq (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ) (key : Nat) :
    runCallback interp fuel m program context key =
      (drive interp fuel
        { m with
          fibers := m.fibers ++
            [{ RunFiber.make ⟨m.nextId⟩ program true (interp.budgetOf context) context with
                observers := [Observer.callback key] }]
          nextId := m.nextId + 1 }
        [Cmd.evaluate ⟨m.nextId⟩, Cmd.drainDue], ⟨m.nextId⟩) := rfl

/-- The callback observer delivers the exit as an event under its key (`runCallbackWith`'s
`onExit`). census: entry.run-callback-with -/
theorem fireObserver_callback (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St) (nested : List (Cmd ν σ β ε δ ι α))
    (key : Nat) :
    fireObserver interp id exit (m, nested) (Observer.callback key) =
      ((m.emit [RunEvent.observerFired id (Observer.callback key)]).emit [RunEvent.callback key exit], nested) := rfl

/-- The abort signal (`:5425-5433`): an interrupt with no interruptor id.
census: entry.abort-signal -/
theorem stepDecision_abort (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (annotations : ReasonAnnotations α) (target : FiberId)
    (t : RunFiber ν σ β ε δ ι α χ) (ht : m.fiber? target = some t) :
    stepDecision interp fuel m (RunDecision.interruptFrom none annotations target) =
      (let r := interruptRecord interp none annotations t
       let m := m.emit [RunEvent.interruptRecorded none target]
       let m := if r.1.frame.deferredInterrupt && r.1.running then
         m.emit [RunEvent.interruptDeferred target] else m
       let m := m.update r.1
       if r.2 then drive interp fuel m [Cmd.evaluate target, Cmd.drainDue] else m) := by
  simp only [stepDecision, stepDecisionState, stepDecisionState.loop, drive, ht]
  split <;> rfl

/-- `runSyncExitWith` (`:5535-5545`): the root is forked and the *root's* dispatcher flushed
(`fiber._dispatcher?.flush()`, `:5542`; R2-14); the root's exit is the answer.
census: entry.run-sync-exit-with -/
theorem runSyncExit_exited (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ)
    (exit : Exit β ε δ ι α)
    (h : (((stepDecision.flushRoot interp fuel (runFork interp fuel m program context).2 fuel
        (runFork interp fuel m program context).1).fiber?
        (runFork interp fuel m program context).2).bind RunFiber.exit) = some exit) :
    (runSyncExit interp fuel m program context).2 = exit := by
  simp [runSyncExit, h]

/-- A root that has not exited after its own dispatcher is flushed is the `AsyncFiberError`
defect (`:5543`) — a child parked on its *own* dispatcher is not run (R2-14).
census: entry.async-fiber-error -/
theorem runSyncExit_survives (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ)
    (h : (((stepDecision.flushRoot interp fuel (runFork interp fuel m program context).2 fuel
        (runFork interp fuel m program context).1).fiber?
        (runFork interp fuel m program context).2).bind RunFiber.exit) = none) :
    (runSyncExit interp fuel m program context).2 = Exit.failure (Cause.die interp.asyncFiberError) := by
  simp [runSyncExit, h]

/-- `runPromiseExitWith` resolves with the exit, `runPromiseWith` rejects with `causeSquash`
(`:5493-5525`). census: entry.run-promise-exit-with -/
theorem promiseOutcome_eq (value : β) (cause : Cause ε δ ι α) :
    promiseOutcome (Exit.success value : Exit β ε δ ι α) = Except.ok value ∧
      promiseOutcome (Exit.failure cause : Exit β ε δ ι α) = Except.error cause.squash :=
  ⟨rfl, rfl⟩

/-- The squash is the projection, never the exit (`:5510-5525`). census: entry.run-promise-with -/
theorem promiseOutcome_failure (cause : Cause ε δ ι α) :
    promiseOutcome (Exit.failure cause : Exit β ε δ ι α) = Except.error cause.squash := rfl

/-! ## Second pass (2026-09-04): the exit path, the observers, the races and the fork arms

These clauses close the rows that were witnessed only by the retired supervision calculus:
`fork.child`, `fork.detach`, `fork.in`, `fork.scoped`, `fork.race-all`, `fork.interrupt`,
`fork.interrupt-all`, `interrupt.accumulate`, `rule.only-fork-child-tracks`,
`rule.children-interrupted-after-exit`, the three `scope.close-*` rows and `op.Async`. The
branches of `exitFiber` and the settling arm of a race callback are named as definitions so
that a clause can be a projection of a branch rather than a hypothesis-laden equation. -/

namespace RunMachine

/-- Emitting events touches only the trace. -/
theorem fiber?_emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ))
    (id : FiberId) : (m.emit events).fiber? id = m.fiber? id := rfl

theorem race?_emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ))
    (id : Nat) : (m.emit events).race? id = m.race? id := rfl

theorem state_emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ)) :
    (m.emit events).state = m.state := rfl

theorem stuck_emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ)) :
    (m.emit events).stuck = m.stuck := rfl

end RunMachine

/-! `interruptEach` (`Fibers.lean`) is the one interrupt fold every site runs: the exit path's
children (`:613-617`), `fiberInterruptAll` (`:892-896`), a fail-fast countdown, a race
cleanup. -/

/-- No targets, nothing recorded. census: fork.interrupt-all -/
theorem interruptEach_nil (interp : RunInterp ν σ β ε δ ι α χ St) (who : FiberId)
    (extra : ReasonAnnotations α)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) :
    interruptEach interp who extra [] acc = acc := rfl

/-- The requests are executed in list order: the head first, then the rest over the machine
the head left (`:5449`, `for (const child of fibers) child.unsafeInterrupt(...)`).
census: fork.interrupt-all -/
theorem interruptEach_cons (interp : RunInterp ν σ β ε δ ι α χ St) (who t : FiberId)
    (extra : ReasonAnnotations α) (ts : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) :
    interruptEach interp who extra (t :: ts) acc =
      interruptEach interp who extra ts
        (match acc.1.fiber? t with
          | none => acc
          | some g =>
            let r := interruptRecord interp (some who) extra g
            ((acc.1.update r.1).emit [RunEvent.interruptRecorded (some who) t],
          acc.2 ++ (if r.2 then [Cmd.evaluate t] else []))) := by
  simp only [interruptEach, List.foldl_cons]
  congr 1
  split <;> simp_all

/-- A known target is recorded with `who` and the caller's annotations (`:892-895`: the
caller's `fiberStackAnnotations`, whoever the interruptor is), and evaluated now only when
the record applies now (`interruptRecord`). census: fork.interrupt-all -/
theorem interruptEach_known (interp : RunInterp ν σ β ε δ ι α χ St) (who t : FiberId)
    (extra : ReasonAnnotations α) (ts : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (g : RunFiber ν σ β ε δ ι α χ) (h : acc.1.fiber? t = some g) :
    interruptEach interp who extra (t :: ts) acc =
      interruptEach interp who extra ts
        (let r := interruptRecord interp (some who) extra g
         ((acc.1.update r.1).emit [RunEvent.interruptRecorded (some who) t],
           acc.2 ++ (if r.2 then [Cmd.evaluate t] else []))) := by
  simp only [interruptEach_cons, h]

/-- The exit path is the two clauses, chosen by the middleware, the finalizing flag and the
tracked children (`:611-627`). census: rule.children-interrupted-after-exit -/
theorem exitFiber_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    exitFiber interp m f exit =
      if m.middlewareInstalled && f.finalizing.isNone && !f.children.isEmpty then
        exitFiber.exitInterruptChildren interp m f exit
      else exitFiber.exitStore interp m f exit := rfl

/-- Without the middleware the exit is published at once: the children survive (`:611`).
census: fork.child -/
theorem exitFiber_no_middleware (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (h : m.middlewareInstalled = false) :
    exitFiber interp m f exit = exitFiber.exitStore interp m f exit := by
  rw [exitFiber_eq]; simp [h]

/-- A fiber with no tracked children publishes its exit at once, whatever the middleware: a
daemon child is never tracked (`spawn_untracked`, `drive_trackChild_*`), so a parent's exit
never reaches it (`:613`). census: fork.detach -/
theorem exitFiber_no_children (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (h : f.children = []) :
    exitFiber interp m f exit = exitFiber.exitStore interp m f exit := by
  rw [exitFiber_eq]; simp [h]

/-- A fiber already finalizing publishes the exit it is now given (`:612`): the re-entry's
program restores the body's exit, and an interrupt that lands while the children are awaited
replaces it with its own failure. census: rule.children-interrupted-after-exit -/
theorem exitFiber_finalizing (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit body : Exit β ε δ ι α)
    (h : f.finalizing = some body) :
    exitFiber interp m f exit = exitFiber.exitStore interp m f exit := by
  rw [exitFiber_eq]; simp [h]

/-- With the middleware installed, not finalizing, and tracked children, the children clause
runs (`:613`). census: rule.children-interrupted-after-exit -/
theorem exitFiber_children (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (hm : m.middlewareInstalled = true) (hf : f.finalizing = none)
    (hc : f.children.isEmpty = false) :
    exitFiber interp m f exit = exitFiber.exitInterruptChildren interp m f exit := by
  rw [exitFiber_eq]; simp [hm, hf, hc]

/-- The published fiber (`:619`, D6b): the exit stored, the finalizing flag, the parks and
the loop's deferred flag cleared, not running; stack, children, observers and context are
kept for the observers. census: fork.child -/
theorem publish_fields (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (f.publish exit).exit = some exit ∧ (f.publish exit).finalizing = none ∧
      (f.publish exit).running = false ∧ (f.publish exit).parked = Parked.notParked ∧
      (f.publish exit).pending = [] ∧ (f.publish exit).frame.deferredInterrupt = false ∧
      (f.publish exit).frame.stack = f.frame.stack ∧ (f.publish exit).children = f.children ∧
      (f.publish exit).observers = f.observers ∧ (f.publish exit).context = f.context :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The cleared fiber (`:624-627`): observers, stack, children and context emptied, the exit
kept. census: fork.child -/
theorem cleared_fields (interp : RunInterp ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) :
    (f.cleared interp).observers = [] ∧ (f.cleared interp).frame.stack = [] ∧
      (f.cleared interp).children = [] ∧ (f.cleared interp).context = interp.emptyContext ∧
      (f.cleared interp).exit = f.exit := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A fiber with no observer is published and cleared in one step, and only the due drain
follows (`:619-627`): the straight fragment's exit cost. census: fork.child -/
theorem exitStore_no_observers (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (h : f.observers = []) :
    exitFiber.exitStore interp m f exit =
      (((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]).update
        ((f.publish exit).cleared interp), [Cmd.drainDue]) := by
  simp [exitFiber.exitStore, RunFiber.publish, h]

/-- With observers, the exit is published and each observer is a command in index order, each
fired on the machine its predecessors left, before the fiber is cleared and the due resumes
drained (`:619-627`, D6b). census: fork.child -/
theorem exitStore_observers (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (o : Observer) (os : List Observer) (h : f.observers = o :: os) :
    exitFiber.exitStore interp m f exit =
      ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit],
        (o :: os).map (Cmd.observe f.id exit) ++ [Cmd.exitDone f.id, Cmd.drainDue]) := by
  simp [exitFiber.exitStore, RunFiber.publish, h]

/-- One observer command (`:621-623`, D6b): `fireObserver` on the current machine, and what
it owes runs before the next observer. census: fork.child -/
theorem drive_observe (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (exit : Exit β ε δ ι α)
    (observer : Observer) (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) :
    drive interp (fuel + 1) m (Cmd.observe id exit observer :: rest) =
      (let r := fireObserver interp id exit (m, []) observer
       drive interp fuel r.1 (r.2 ++ rest)) := by
  simp [drive, driveState, driveStep, hs]

/-- The end of the exit path (`:624-627`, D6b): the fiber is re-read and cleared.
census: fork.child -/
theorem drive_exitDone (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f) :
    drive interp (fuel + 1) m (Cmd.exitDone id :: rest) =
      drive interp fuel (m.update (f.cleared interp)) rest := by
  simp [drive, driveState, driveStep, hs, hf]

/-- The children clause, spelled out (`:613-617`, D6b): the parent remembers the exit it is
finalizing, its deferred flag is cleared, the middleware's program
`flatMap(fiberInterruptAll(children), () => exit)` is installed, the `childrenInterrupted`
event is emitted, and the counted re-entry is the one command.
census: rule.children-interrupted-after-exit -/
theorem exitInterruptChildren_eq (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    exitFiber.exitInterruptChildren interp m f exit =
      ((m.update { f with
          finalizing := some exit
          running := false
          frame := { f.frame with
            deferredInterrupt := false
            current := Prim.onSuccess (interp.interruptAllCode f.children) (interp.restoreName exit) } }).emit
        [RunEvent.childrenInterrupted f.id f.children],
       [Cmd.evaluate f.id]) := rfl

/-- The re-entry is `evaluate` (`:615`): a new counted entry, on the fiber now finalizing.
census: rule.children-interrupted-after-exit -/
theorem exitInterruptChildren_reenters (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (exitFiber.exitInterruptChildren interp m f exit).2 = [Cmd.evaluate f.id] := rfl

/-- A countdown keeps the fiber's finalizing flag, parked or not. -/
theorem countdownPark_finalizing (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId)
    (resumeWith : Resume ν) (failFast : Bool) :
    (countdownPark interp m f targets resumeWith failFast).2.1.finalizing = f.finalizing := by
  simp only [countdownPark]
  rcases countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
    ⟨exits, _ | ⟨target, remaining⟩⟩ <;> rfl

/-- A finished countdown that continues with a name resumes with the collected exits fed to
that name (`:617`, the parent's `flatMap(awaitAllChildren, () => exit)`).
census: rule.children-interrupted-after-exit -/
theorem resumePrim_continueWith (interp : RunInterp ν σ β ε δ ι α χ St) (name : ν)
    (exits : List (Exit β ε δ ι α)) :
    countdownPark.resumePrim interp (Resume.continueWith name) exits =
      Prim.onSuccess (Prim.success (interp.exitsValue exits)) name := rfl

/-- Installing the middleware is a flag on the machine (`FiberMiddleware`, `:611`).
census: fork.child -/
theorem stepDecision_installMiddleware (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) :
    stepDecision interp fuel m RunDecision.installMiddleware = { m with middlewareInstalled := true } :=
  rfl

/-- A child's completion resumes its awaiter with the exit in the awaiter's mode
(`:561-562`, `:5291`, `:5304`): the resume is a command, run synchronously. census: fork.child -/
theorem fireObserver_resumeAwait (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (waiter : FiberId) (token : Nat) (mode : Supervision.ObserverMode) :
    fireObserver interp id exit acc (Observer.resumeAwait waiter token mode) =
      (acc.1.emit [RunEvent.observerFired id (Observer.resumeAwait waiter token mode)],
        acc.2 ++ [Cmd.resume waiter token (interp.exitValue exit mode)]) := rfl

/-- A tracked child's completion removes it from its parent's children (`:5281`).
census: rule.only-fork-child-tracks -/
theorem fireObserver_untrackChild (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (parent : FiberId) :
    fireObserver interp id exit acc (Observer.untrackChild parent) =
      ((acc.1.emit [RunEvent.observerFired id (Observer.untrackChild parent)]).modify parent
          (fun p => { p with children := p.children.filter fun c => c ≠ id }), acc.2) := rfl

/-- A scope-linked fiber's completion drops its keyed finalizer from the scope (`:5370-5372`).
census: fork.in -/
theorem fireObserver_dropScopeFinalizer (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (scope key : Nat) (state : St) (h : interp.dropFinalizer scope key acc.1.state = some state) :
    fireObserver interp id exit acc (Observer.dropScopeFinalizer scope key) =
      ({ acc.1.emit [RunEvent.observerFired id (Observer.dropScopeFinalizer scope key)] with
          state := state }, acc.2) := by
  simp [fireObserver, RunMachine.state_emit, h]

/-- `fiberAwaitAll`'s walk (`:794-808`, R2-4) on an empty list: every exit, nothing to
observe. census: fork.await-all-children -/
theorem countdownWalk_nil (m : RunMachine ν σ β ε δ ι α χ St) (exits : List (Exit β ε δ ι α)) :
    countdownWalk m [] exits = (exits, none) := rfl

/-- An exited target's exit is collected in place and the walk goes on (`:797-800`).
census: fork.await-all-children -/
theorem countdownWalk_exited (m : RunMachine ν σ β ε δ ι α χ St) (t : FiberId)
    (rest : List FiberId) (exits : List (Exit β ε δ ι α)) (g : RunFiber ν σ β ε δ ι α χ)
    (exit : Exit β ε δ ι α) (hg : m.fiber? t = some g) (hexit : g.exit = some exit) :
    countdownWalk m (t :: rest) exits = countdownWalk m rest (exits ++ [exit]) := by
  simp [countdownWalk, hg, hexit]

/-- The first live target stops the walk: it is the one to observe, with the targets after
it (`:802`). census: fork.await-all-children -/
theorem countdownWalk_live (m : RunMachine ν σ β ε δ ι α χ St) (t : FiberId)
    (rest : List FiberId) (exits : List (Exit β ε δ ι α)) (g : RunFiber ν σ β ε δ ι α χ)
    (hg : m.fiber? t = some g) (hlive : g.exit = none) :
    countdownWalk m (t :: rest) exits = (exits, some (t, rest)) := by
  simp [countdownWalk, hg, hlive]

/-- A countdown with no live target answers the exits at once, in input order (`:806`),
without parking. census: fork.await-all-children -/
theorem countdownPark_none_live (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId)
    (resumeWith : Resume ν) (failFast : Bool) (exits : List (Exit β ε δ ι α))
    (hwalk : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] = (exits, none)) :
    countdownPark interp m f targets resumeWith failFast =
      ({ m with nextToken := m.nextToken + 1 },
        { f with frame := { f.frame with current := countdownPark.resumePrim interp resumeWith exits } },
        false) := by
  simp [countdownPark, hwalk]

/-- A countdown with a live target observes that one target only, pushes the park's cleanup
as an `AsyncFinalizer` frame (`:812`, `:1128-1141`; R2-3), and parks with the rest of the
walk pending (`:802`; R2-4). census: fork.await-all-children -/
theorem countdownPark_parks (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId)
    (resumeWith : Resume ν) (failFast : Bool) (exits : List (Exit β ε δ ι α)) (target : FiberId)
    (remaining : List FiberId)
    (hwalk : countdownWalk { m with nextToken := m.nextToken + 1 } targets [] =
      (exits, some (target, remaining))) :
    countdownPark interp m f targets resumeWith failFast =
      (let m' : RunMachine ν σ β ε δ ι α χ St := { m with nextToken := m.nextToken + 1 }
       let name := interp.cancelName interp.parkCancelName f.id m.nextToken
       let g := ({ f with frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack } }).park
         ⟨m.nextToken, some target, remaining, exits, resumeWith, failFast⟩
       ((m'.modify target fun g => { g with observers := g.observers ++ [Observer.countdown f.id m.nextToken] }).emit
          [RunEvent.parkedOn f.id m.nextToken], g, true)) := by
  simp only [countdownPark, hwalk]
  try rfl

/-- The observed target's exit is collected and the walk goes on; when nothing after it is
live the awaiter is resumed with every exit, in input order (`:806`, `:779`; `:5449`, the
explicit await after the requests). census: fork.await-all-children -/
theorem fireObserver_countdown_done (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (waiter : FiberId) (token : Nat) (w : RunFiber ν σ β ε δ ι α χ) (p : Pending ν β ε δ ι α)
    (exits : List (Exit β ε δ ι α))
    (hw : acc.1.fiber? waiter = some w) (hp : w.pending.find? (fun q => q.token = token) = some p)
    (hff : p.failFast = false)
    (hwalk : countdownWalk (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)])
      p.remaining (p.collected ++ [exit]) = (exits, none)) :
    fireObserver interp id exit acc (Observer.countdown waiter token) =
      ((acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)]).update
          { w with pending := w.pending.map fun q =>
              if q.token = token then
                { q with waitingOn := none, remaining := [], collected := exits }
              else q },
        acc.2 ++ [Cmd.resume waiter token (countdownPark.resumePrim interp p.resumeWith exits)]) := by
  simp [fireObserver, RunMachine.fiber?_emit, hw, hp, hff, hwalk]

/-- … and when a later target is live, the countdown moves its one observer to it
(`:802`, `loop()` at `:804`). census: fork.await-all-children -/
theorem fireObserver_countdown_next (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (waiter : FiberId) (token : Nat) (w : RunFiber ν σ β ε δ ι α χ) (p : Pending ν β ε δ ι α)
    (exits : List (Exit β ε δ ι α)) (next : FiberId) (rest : List FiberId)
    (hw : acc.1.fiber? waiter = some w) (hp : w.pending.find? (fun q => q.token = token) = some p)
    (hff : p.failFast = false)
    (hwalk : countdownWalk (acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)])
      p.remaining (p.collected ++ [exit]) = (exits, some (next, rest))) :
    fireObserver interp id exit acc (Observer.countdown waiter token) =
      (((acc.1.emit [RunEvent.observerFired id (Observer.countdown waiter token)]).modify next
          (fun g => { g with observers := g.observers ++ [Observer.countdown waiter token] })).update
          { w with pending := w.pending.map fun q =>
              if q.token = token then
                { q with waitingOn := some next, remaining := rest, collected := exits }
              else q },
        acc.2) := by
  simp [fireObserver, RunMachine.fiber?_emit, hw, hp, hff, hwalk]

/-- The settling arm of a race callback (`:1503-1514`, R2-12): the race is marked settled;
while its registration is still running the answer is only buffered (`:1120-1126`, D6a),
otherwise the host is resumed on its race guard with `interp.raceSettle raceId
state.cleanupNeeded accepted` — `flatMap(uninterruptible(fiberInterruptAll(fibers)), () =>
exit)` over the race's live set at cleanup time when the callback saw one, or the exit
alone. -/
def settleRace (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (acc : List (Cmd ν σ β ε δ ι α)) (raceId : Nat) (race : Race ν σ β ε δ ι α)
    (state : Supervision.RaceAllState β ε δ ι α) (accepted : Exit β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α) :=
  let m := m.updateRace { race with settled := true }
  let m := m.emit [RunEvent.raceSettled raceId accepted]
  (m, acc ++ (if race.registering then [] else
    [Cmd.resume race.host race.token (interp.raceSettle raceId state.cleanupNeeded accepted)]))

/-- The settle resumes the host, and nothing else: no entrant is touched until the host runs
the program it was resumed with (`:1510-1514`); during registration it resumes nothing and
`registrationDone` takes the buffered answer up (D6a). census: fork.race-all -/
theorem settleRace_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (acc : List (Cmd ν σ β ε δ ι α)) (raceId : Nat) (race : Race ν σ β ε δ ι α)
    (state : Supervision.RaceAllState β ε δ ι α) (accepted : Exit β ε δ ι α) :
    settleRace interp m acc raceId race state accepted =
      ((m.updateRace { race with settled := true }).emit [RunEvent.raceSettled raceId accepted],
        acc ++ (if race.registering then [] else
          [Cmd.resume race.host race.token
            (interp.raceSettle raceId state.cleanupNeeded accepted)])) := rfl

/-- The first accepted callback settles the race: the frozen bookkeeping accepts, the race was
not yet settled, and the settling arm runs over the updated race. census: fork.race-all -/
theorem fireObserver_raceCallback_settles (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (raceId : Nat) (race : Race ν σ β ε δ ι α) (accepted : Exit β ε δ ι α)
    (hr : acc.1.race? raceId = some race)
    (hacc : (Supervision.raceComplete race.state id exit).accepted = some accepted)
    (hset : race.settled = false) :
    fireObserver interp id exit acc (Observer.raceCallback raceId) =
      (let state := Supervision.raceComplete race.state id exit
       let race := { race with state := state }
       settleRace interp
         ((acc.1.emit [RunEvent.observerFired id (Observer.raceCallback raceId)]).updateRace race)
         acc.2 raceId race state accepted) := by
  simp only [fireObserver, RunMachine.race?_emit, hr, hacc, hset]
  try rfl

/-- A callback after the race has settled only updates the frozen bookkeeping: the first
accepted result is stable (`race_first_accepted_stable`). census: fork.race-all -/
theorem fireObserver_raceCallback_late (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (raceId : Nat) (race : Race ν σ β ε δ ι α)
    (hr : acc.1.race? raceId = some race) (hset : race.settled = true) :
    fireObserver interp id exit acc (Observer.raceCallback raceId) =
      ((acc.1.emit [RunEvent.observerFired id (Observer.raceCallback raceId)]).updateRace
        { race with state := Supervision.raceComplete race.state id exit }, acc.2) := by
  simp only [fireObserver, RunMachine.race?_emit, hr, hset]
  cases (Supervision.raceComplete race.state id exit).accepted <;> rfl

/-- A callback that does not yet accept (a loser before the winner) only updates the frozen
bookkeeping. census: fork.race-all -/
theorem fireObserver_raceCallback_pending (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (raceId : Nat) (race : Race ν σ β ε δ ι α)
    (hr : acc.1.race? raceId = some race)
    (hacc : (Supervision.raceComplete race.state id exit).accepted = none) :
    fireObserver interp id exit acc (Observer.raceCallback raceId) =
      ((acc.1.emit [RunEvent.observerFired id (Observer.raceCallback raceId)]).updateRace
        { race with state := Supervision.raceComplete race.state id exit }, acc.2) := by
  simp only [fireObserver, RunMachine.race?_emit, hr, hacc]

/-- A launch after the race has accepted forks nothing: the register loop has broken
(`if (done) break`, `:1527`; R2-11), and the entrant that was next never exists.
census: fork.race-all -/
theorem drive_launch_done (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (rest : List (Cmd ν σ β ε δ ι α))
    (race : Race ν σ β ε δ ι α) (accepted : Exit β ε δ ι α) (program : Prim ν σ β ε δ ι α)
    (more : List (Prim ν σ β ε δ ι α))
    (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hp : race.programs = program :: more) (hacc : race.state.accepted = some accepted) :
    drive interp (fuel + 1) m (Cmd.launch raceId :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hr, hp, hacc]

/-- A launch with no entrant left is the end of the register loop. census: fork.race-all -/
theorem drive_launch_exhausted (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (rest : List (Cmd ν σ β ε δ ι α))
    (race : Race ν σ β ε δ ι α) (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hp : race.programs = []) :
    drive interp (fuel + 1) m (Cmd.launch raceId :: rest) = drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hr, hp]

/-- A launch before the race has accepted forks the next entrant over the host, evaluates it
now (`forkUnsafe(…, true, …)`, `:1521`), enrolls it after that run returns (`:1522-1526`,
D6a) and goes round again (`:1520-1528`). census: fork.race-all -/
theorem drive_launch_runs (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (rest : List (Cmd ν σ β ε δ ι α))
    (race : Race ν σ β ε δ ι α) (program : Prim ν σ β ε δ ι α) (more : List (Prim ν σ β ε δ ι α))
    (host : RunFiber ν σ β ε δ ι α χ)
    (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hp : race.programs = program :: more) (hacc : race.state.accepted = none)
    (hh : m.fiber? race.host = some host) :
    drive interp (fuel + 1) m (Cmd.launch raceId :: rest) =
      (let l := launchEntrant interp raceId m host program
       drive interp fuel
         ((l.1.updateRace { race with programs := more }).emit [RunEvent.raceLaunched raceId l.2])
         (Cmd.evaluate l.2 :: Cmd.enrollRace raceId l.2 :: Cmd.launch raceId :: rest)) := by
  simp [drive, driveState, driveStep, hs, hr, hp, hacc, hh]

/-- An entrant's enrollment after its immediate run (`:1522-1526`, D6a): it joins the race's
live set and, still live, gets the race callback as its observer. census: fork.race-all -/
theorem drive_enrollRace_live (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (child : FiberId)
    (rest : List (Cmd ν σ β ε δ ι α)) (race : Race ν σ β ε δ ι α) (c : RunFiber ν σ β ε δ ι α χ)
    (hs : m.stuck = none) (hr : m.race? raceId = some race) (hc : m.fiber? child = some c)
    (hlive : c.exit = none) :
    drive interp (fuel + 1) m (Cmd.enrollRace raceId child :: rest) =
      drive interp fuel
        ((m.updateRace { race with state := { race.state with live := race.state.live ++ [child] } }).modify
          child fun c => { c with observers := c.observers ++ [Observer.raceCallback raceId] })
        rest := by
  simp [drive, driveState, driveStep, hs, hr, hc, hlive]

/-- An entrant that exited during its immediate run is enrolled and its race callback fires
at once (`addObserver` on an exited fiber, `:557-559`; D6a). census: fork.race-all -/
theorem drive_enrollRace_exited (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (child : FiberId)
    (rest : List (Cmd ν σ β ε δ ι α)) (race : Race ν σ β ε δ ι α) (c : RunFiber ν σ β ε δ ι α χ)
    (exit : Exit β ε δ ι α)
    (hs : m.stuck = none) (hr : m.race? raceId = some race) (hc : m.fiber? child = some c)
    (hexit : c.exit = some exit) :
    drive interp (fuel + 1) m (Cmd.enrollRace raceId child :: rest) =
      (let r := fireObserver interp child exit
        (m.updateRace { race with state := { race.state with live := race.state.live ++ [child] } }, [])
        (Observer.raceCallback raceId)
       drive interp fuel r.1 (r.2 ++ rest)) := by
  simp [drive, driveState, driveStep, hs, hr, hc, hexit]

/-- The registration returns with a buffered answer (`:1120-1126`, D6a): the host continues
its entry with the settle program, count and latch retained. census: fork.race-all -/
theorem drive_registrationDone_answered (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (yielding : Bool)
    (rest : List (Cmd ν σ β ε δ ι α)) (race : Race ν σ β ε δ ι α) (host : RunFiber ν σ β ε δ ι α χ)
    (accepted : Exit β ε δ ι α)
    (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hh : (m.updateRace { race with registering := false }).fiber? race.host = some host)
    (hacc : race.state.accepted = some accepted) :
    drive interp (fuel + 1) m (Cmd.registrationDone raceId yielding :: rest) =
      drive interp fuel
        ((m.updateRace { race with registering := false }).update
          { host with frame := { host.frame with
              current := interp.raceSettle raceId race.state.cleanupNeeded accepted } })
        (Cmd.loop host.id yielding :: rest) := by
  simp [drive, driveState, driveStep, settle, hs, hr, hh, hacc]

/-- The registration returns without an answer (`:1128-1141`, D6a): the host pushes the
race's cancel as an `AsyncFinalizer` frame and parks on the race guard. census: fork.race-all -/
theorem drive_registrationDone_parks (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (yielding : Bool)
    (rest : List (Cmd ν σ β ε δ ι α)) (race : Race ν σ β ε δ ι α) (host : RunFiber ν σ β ε δ ι α χ)
    (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hh : (m.updateRace { race with registering := false }).fiber? race.host = some host)
    (hacc : race.state.accepted = none) (hd : host.frame.deferredInterrupt = false) :
    drive interp (fuel + 1) m (Cmd.registrationDone raceId yielding :: rest) =
      (let name := interp.cancelName (interp.raceCancelName raceId) host.id race.token
       let g := ({ host with frame := { host.frame with
          stack := Prim.asyncFinalizer name :: host.frame.stack } }).park
         ⟨race.token, none, [], [], Resume.void, false⟩
       drive interp fuel
         (((m.updateRace { race with registering := false }).emit [RunEvent.parkedOn g.id race.token]).update
           { g with running := false })
         rest) := by
  simp [drive, driveState, driveStep, settle, RunFiber.park, FiberCore.pushAsyncFinalizer,
    FiberCore.deferredInterrupt, hs, hr, hh, hacc, hd]

/-- `forkIn`'s link as a command (`:5366-5376`, R2-8): `linkScope` over the re-read child,
whatever it owes first. census: fork.in -/
theorem drive_link (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) :
    drive interp (fuel + 1) m (Cmd.link mode scope target interruptor extra :: rest) =
      (let l := linkScope interp m mode scope target interruptor extra
       drive interp fuel l.1 (l.2 ++ rest)) := by
  simp [drive, driveState, driveStep, hs]

/-- `fork` (`:5264-5284`): a non-daemon fork installs the interrupt-children middleware
(`forkChild`, `:5253`), then spawn with the options as given, start by `startImmediately`,
answer the child's handle, and — unless daemon — track the child by a command after its
immediate run or its scheduling (`:5279-5282`, D6b). census: fork.child -/
theorem withFiber_fork (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.fork program options) =
      (let m' := if options.daemon then m else { m with middlewareInstalled := true }
       let s := spawn interp m' f program options
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_,
        t.2.2 ++ (if options.daemon then [] else [Cmd.trackChild f.id s.2.2])⟩) := rfl

/-- `forkIn` (`:5364-5378`): the child is a daemon of its parent, started by
`startImmediately`, and *then* linked to the supplied scope by number — with the parent as
interruptor and the parent's stack annotations — by a command after its start, so an
immediately finished child is never linked (`:5366-5376`, R2-8). census: fork.in -/
theorem withFiber_forkIn (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (scope : Nat) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkIn program options scope) =
      (let s := spawn interp m f program { options with daemon := true }
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_,
        t.2.2 ++ [Cmd.link Supervision.ScopeMode.forkIn scope s.2.2 (some t.2.1.id)
          (interp.stackAnnotations t.2.1.id)]⟩) := rfl

/-- `forkScoped` (`:5400-5406`) resolves the ambient `Scope` service of the parent's context
and is then `forkIn` on it. census: fork.scoped -/
theorem withFiber_forkScoped_ambient (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (h : interp.ambientScope f.context = some scope) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options) =
      (let s := spawn interp m f program { options with daemon := true }
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_,
        t.2.2 ++ [Cmd.link Supervision.ScopeMode.forkIn scope s.2.2 (some t.2.1.id)
          (interp.stackAnnotations t.2.1.id)]⟩) := by
  simp only [evaluatePrim.withFiber, h]
  try rfl

/-- Without an ambient `Scope` service `forkScoped` dies with the `missingScope` defect: the
service is required (`:5400`, `Context.get` throws `ServiceNotFound`); it is not the
"unimplemented step" defect (finding S1-1, 2026-09-04). census: fork.scoped -/
theorem withFiber_forkScoped_none (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions)
    (h : interp.ambientScope f.context = none) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options) =
      ⟨m, { f with frame := { f.frame with
          current := Prim.failure (Cause.die interp.missingScope) } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber, h]

/-- Linking to an open scope registers the keyed finalizer in the store and the key-dropping
observer on the fiber (`:5369-5372`, `:5458`). census: fork.in -/
theorem linkScope_open (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (state : St) (key : Nat) (t : RunFiber ν σ β ε δ ι α χ)
    (hopen : interp.scopeStatus scope m.state = some none)
    (ht : m.fiber? target = some t) (hlive : t.exit = none)
    (hlink : interp.scopeLinkFiber mode scope target m.state = some (state, key)) :
    linkScope interp m mode scope target interruptor extra =
      (RunMachine.emit
        (RunMachine.modify { m with state := state } target fun t =>
          { t with observers := t.observers ++ [Observer.dropScopeFinalizer scope key] })
        [RunEvent.scopeLinked mode scope key target], []) := by
  simp [linkScope, hopen, ht, hlive, hlink]

/-- An exited fiber is not linked (`:5367`, `:5451-5452`; R2-9). census: fork.fiber-run-in -/
theorem linkScope_open_exited (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (t : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (hopen : interp.scopeStatus scope m.state = some none)
    (ht : m.fiber? target = some t) (hexited : t.exit = some exit) :
    linkScope interp m mode scope target interruptor extra = (m, []) := by
  simp [linkScope, hopen, ht, hexited]

/-- Closing a scope installs the store's close program as the closer's current primitive
(`Scope.close`): the sequential strategy's chain awaits each finalizer through its exit and
the parallel strategy's forks run on this machine. census: scope.close-sequential -/
theorem withFiber_closeScope (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (scope : Nat) (exit : Exit β ε δ ι α) (state : St) (program : Prim ν σ β ε δ ι α)
    (h : interp.closeScope scope exit f.frame.interruptible f.id m.state = some (state, program)) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.closeScope scope exit) =
      ⟨{ m with state := state }, { f with frame := { f.frame with current := program } },
        yielding, Outcome.continue_, []⟩ := by
  simp [evaluatePrim.withFiber, h]

/-- Closing an unknown scope halts the machine (M7). census: scope.close-sequential -/
theorem withFiber_closeScope_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (scope : Nat) (exit : Exit β ε δ ι α)
    (h : interp.closeScope scope exit f.frame.interruptible f.id m.state = none) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.closeScope scope exit) =
      ⟨m, f, yielding, Outcome.stuck (Stuck.unknownScope scope), []⟩ := by
  simp [evaluatePrim.withFiber, h]

/-- `fiberInterrupt` (`:857`, D6b): the public `withFiber` returns `fiberInterruptAs(target,
fiber.id)` as the next counted program; nothing is recorded yet. census: fork.interrupt -/
theorem withFiber_interrupt (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interrupt target) =
      ⟨m, { f with frame := { f.frame with current := interp.interruptAsCode target f.id } },
        yielding, Outcome.continue_, []⟩ := rfl

/-- `fiberInterruptAs(target, who)` (`:871-884`, D6b): the record with `who` and the caller's
stack annotations (`:880-883`, R2-5), then the commands: the target's own run when the record
applies now, and the return that constructs `asVoid(fiberAwait(target))` afterwards.
census: fork.interrupt -/
theorem withFiber_interruptAs (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target who : FiberId) (t : RunFiber ν σ β ε δ ι α χ) (ht : m.fiber? target = some t) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptAs target who) =
      (let r := interruptRecord interp (some who) (interp.stackAnnotations f.id) t
       ⟨(m.update r.1).emit [RunEvent.interruptRecorded (some who) target], f, yielding,
        Outcome.commands,
        (if r.2 then [Cmd.evaluate target] else []) ++
          [Cmd.afterInterrupt f.id yielding (ParkKind.join target Supervision.ObserverMode.awaitValue)]⟩) := by
  simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs, ht]

/-- An unknown target is stuck (S3 §5.1). census: fork.interrupt -/
theorem withFiber_interruptAs_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target who : FiberId) (ht : m.fiber? target = none) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptAs target who) =
      ⟨m, f, yielding, Outcome.stuck (Stuck.unknownFiber target), []⟩ := by
  simp [evaluatePrim.withFiber, evaluatePrim.interruptAs, ht]

/-- `interruptUnsafe` as a command (`:574-595`, D6b): the target is re-read and recorded, and
one that applies now is evaluated before the next command. census: fork.interrupt-all -/
theorem drive_interruptTarget (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations α) (g : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hg : m.fiber? target = some g) :
    drive interp (fuel + 1) m (Cmd.interruptTarget target who extra :: rest) =
      (let r := interruptRecord interp who extra g
       drive interp fuel ((m.update r.1).emit [RunEvent.interruptRecorded who target])
         ((if r.2 then [Cmd.evaluate target] else []) ++ rest)) := by
  simp [drive, driveState, driveStep, hs, hg]

/-- An unknown target is skipped by the walk (`interruptEach`'s rule). census: fork.interrupt-all -/
theorem drive_interruptTarget_unknown (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations α) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hg : m.fiber? target = none) :
    drive interp (fuel + 1) m (Cmd.interruptTarget target who extra :: rest) =
      drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hg]

/-- The return of an interrupt (`:884`, `:896`, D6b): the host is re-read and continues its
entry — count and latch retained — with `asVoid` of the await code constructed now.
census: fork.interrupt -/
theorem drive_afterInterrupt (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : FiberId) (yielding : Bool) (kind : ParkKind)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? host = some f) :
    drive interp (fuel + 1) m (Cmd.afterInterrupt host yielding kind :: rest) =
      drive interp fuel
        (m.update { f with frame := { f.frame with
          current := asVoidCode interp (awaitCode interp m kind) } })
        (Cmd.loop f.id yielding :: rest) := by
  simp [drive, driveState, driveStep, settle, hs, hf]

/-- `asVoid(code)` is `flatMap(code, _ => exitVoid)` (`:1467`): the restoring continuation at
the void exit. census: fork.interrupt -/
theorem asVoidCode_eq (interp : RunInterp ν σ β ε δ ι α χ St) (code : Prim ν σ β ε δ ι α) :
    asVoidCode interp code =
      Prim.onSuccess code (interp.restoreName (Exit.success interp.voidValue)) := rfl

/-- `fiberAwait` folds an already exited target at construction (`:767-769`).
census: fork.await -/
theorem awaitCode_join_exited (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (target : FiberId) (mode : Supervision.ObserverMode)
    (t : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) (ht : m.fiber? target = some t)
    (hx : t.exit = some exit) :
    awaitCode interp m (ParkKind.join target mode) = interp.exitValue exit mode := by
  simp [awaitCode, ht, hx]

/-- A live target's await is the join park (`:770-775`). census: fork.await -/
theorem awaitCode_join_live (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (target : FiberId) (mode : Supervision.ObserverMode)
    (t : RunFiber ν σ β ε δ ι α χ) (ht : m.fiber? target = some t) (hx : t.exit = none) :
    awaitCode interp m (ParkKind.join target mode) = interp.parkCode (ParkKind.join target mode) := by
  simp [awaitCode, ht, hx]

/-- `fiberAwaitAll` is always its `callback` (`:779`), also over exited targets.
census: fork.interrupt-all -/
theorem awaitCode_awaitAll (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (targets : List FiberId) :
    awaitCode interp m (ParkKind.awaitAll targets) = interp.parkCode (ParkKind.awaitAll targets) := rfl

/-- The await-all park (`:779-813`, D6b): the countdown over the targets; resumed at once with
the exits when none is live (`:806`), parked on the first live one otherwise.
census: fork.interrupt-all -/
theorem evaluatePrim_awaitAllPark (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (targets : List FiberId) (hcur : f.frame.current = Prim.suspend thunk)
    (hpark : interp.parkOf (Prim.suspend thunk) = some (Except.ok (ParkKind.awaitAll targets))) :
    evaluatePrim interp m f yielding =
      (let p := countdownPark interp m f targets Resume.exitsValue
       ⟨p.1, p.2.1, yielding, (if p.2.2 then Outcome.parked else Outcome.continue_), []⟩) := by
  simp only [evaluatePrim, hcur, hpark]

/-- Interrupting oneself through the scoped entry is a void no-op (`:868`).
census: fork.interrupt -/
theorem withFiber_interruptScoped_self (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptScoped f.id) =
      ⟨m, { f with frame := { f.frame with current := Prim.success interp.voidValue } },
        yielding, Outcome.continue_, []⟩ := by
  simp [evaluatePrim.withFiber]

/-- Any other target through the scoped entry answers the public interrupt program
(`withFiberId(id => … : fiberInterrupt(fiber))`, `:5368`, D6b). census: fork.interrupt -/
theorem withFiber_interruptScoped_other (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) (h : target ≠ f.id) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptScoped target) =
      ⟨m, { f with frame := { f.frame with current := interp.interruptCode target } },
        yielding, Outcome.continue_, []⟩ := by
  simp [evaluatePrim.withFiber, h]

/-- `fiberInterruptAll[As]` (`:888-915`, D6b): one `interruptTarget` per target in list order
with the given interruptor (the caller by default) and the caller's stack annotations, then
the return that constructs `asVoid(fiberAwaitAll(targets))`. census: fork.interrupt-all -/
theorem withFiber_interruptAll (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (targets : List FiberId) (interruptor : Option FiberId) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptAll targets interruptor) =
      ⟨m, f, yielding, Outcome.commands,
        (targets.map fun t =>
          Cmd.interruptTarget t (some (interruptor.getD f.id)) (interp.stackAnnotations f.id)) ++
          [Cmd.afterInterrupt f.id yielding (ParkKind.awaitAll targets)]⟩ := rfl

/-- The entrant's fork, read off the definition: immediate, daemon, interruptible
(`forkUnsafe(parent, effect, true, true, false)`, `:1521`; R2-10), with the race callback as
its observer (`:1523`). census: rule.only-fork-child-tracks -/
theorem launchEntrant_eq (interp : RunInterp ν σ β ε δ ι α χ St) (raceId : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) :
    launchEntrant interp raceId m host program =
      (let s := spawn interp m host program ⟨true, true, Supervision.MaskMode.interruptible⟩
       (s.1, s.2.2)) := rfl

/-- `raceAll` (`:1490-1531`, D6a): the `WithFiber` records the race with its host, its guard
and its entrants still to fork (none exists yet, R2-11) and returns the counted `Async`
registration as the host's next program; nothing is forked or parked in this step. The
register loop, the cancel frame and the park belong to that registration
(`evaluatePrim_raceRegister`, `drive_registrationDone_parks`). census: fork.race-all -/
theorem withFiber_raceAll (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (entrants : List (Prim ν σ β ε δ ι α)) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.raceAll entrants) =
      (let raceId := m.nextRace
       let token := m.nextToken
       let m := { m with nextRace := m.nextRace + 1, nextToken := m.nextToken + 1 }
       let race : Race ν σ β ε δ ι α :=
         ⟨raceId, f.id, token,
           { Supervision.RaceAllState.initial [] with remaining := entrants.length }, false, entrants,
           false⟩
       let m := { m with races := m.races ++ [race] }
       ⟨m.emit [RunEvent.raceStarted raceId f.id entrants.length],
        { f with frame := { f.frame with current := interp.parkCode (ParkKind.race raceId) } },
        yielding, Outcome.continue_, []⟩) :=
  rfl

/-- The race's `Async` registration (`:1117-1141`, `:1520-1528`, D6a): the counted step marks
the race registering and delegates to the register loop and to the registration's return;
the host keeps its code, its count and its latch. census: fork.race-all -/
theorem evaluatePrim_raceRegister (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (raceId : Nat) (race : Race ν σ β ε δ ι α)
    (hcur : f.frame.current = Prim.suspend thunk)
    (hpark : interp.parkOf (Prim.suspend thunk) = some (Except.ok (ParkKind.race raceId)))
    (hr : m.race? raceId = some race) :
    evaluatePrim interp m f yielding =
      ⟨m.updateRace { race with registering := true }, f, yielding, Outcome.commands,
        [Cmd.launch raceId, Cmd.registrationDone raceId yielding]⟩ := by
  simp [evaluatePrim, hcur, hpark, registerRace, hr]

/-- A park's cleanup (`:773`, `:812`, `:821`; R2-3): every observer that would resume this
token, on any fiber, is dropped, and the cleanup answers void. census: fork.await -/
theorem withFiber_dropObservers (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (token : Nat) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.dropObservers token) =
      ⟨{ m with fibers := m.fibers.map fun g =>
          { g with observers := g.observers.filter fun
              | Observer.resumeAwait _ t _ => t ≠ token
              | Observer.countdown _ t => t ≠ token
              | _ => true } },
        { f with frame := { f.frame with current := Prim.success interp.voidValue } },
        yielding, Outcome.continue_, []⟩ := rfl

/-- The race's cleanup (`fiberInterruptAll(fibers)`, `:1512`, `:1530`; R2-13, D6b): the walk
over the entrants live now is a command, so a target an earlier target's run finishes is
skipped. census: fork.race-all -/
theorem withFiber_cancelRace (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (raceId : Nat) (race : Race ν σ β ε δ ι α) (hr : m.race? raceId = some race) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.cancelRace raceId) =
      ⟨m, f, yielding, Outcome.commands, [Cmd.raceCancel raceId f.id yielding race.state.live []]⟩ := by
  simp [evaluatePrim.withFiber, hr]

/-- The Set walk's end (`:896`, D6b): `asVoid(fiberAwaitAll(visited))` over the members visited.
census: fork.race-all -/
theorem drive_raceCancel_nil (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (visited : List FiberId) (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) :
    drive interp (fuel + 1) m (Cmd.raceCancel raceId host yielding [] visited :: rest) =
      drive interp fuel m (Cmd.afterInterrupt host yielding (ParkKind.awaitAll visited) :: rest) := by
  simp [drive, driveState, driveStep, hs]

/-- A member still live is recorded and run, then visited (`:892-895` over the Set, D6b).
census: fork.race-all -/
theorem drive_raceCancel_live (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (t : FiberId) (more visited : List FiberId) (race : Race ν σ β ε δ ι α)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hl : t ∈ race.state.live) :
    drive interp (fuel + 1) m (Cmd.raceCancel raceId host yielding (t :: more) visited :: rest) =
      drive interp fuel m
        (Cmd.interruptTarget t (some host) (interp.stackAnnotations host) ::
          Cmd.raceCancel raceId host yielding more (visited ++ [t]) :: rest) := by
  simp [drive, driveState, driveStep, hs, hr, hl]

/-- A member the race no longer holds live is skipped and not awaited (`fibers.delete`,
`:1525`, D6b). census: fork.race-all -/
theorem drive_raceCancel_gone (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (t : FiberId) (more visited : List FiberId) (race : Race ν σ β ε δ ι α)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hl : t ∉ race.state.live) :
    drive interp (fuel + 1) m (Cmd.raceCancel raceId host yielding (t :: more) visited :: rest) =
      drive interp fuel m (Cmd.raceCancel raceId host yielding more visited :: rest) := by
  simp [drive, driveState, driveStep, hs, hr, hl]

/-- A cleanup for a race the machine does not hold answers void. census: fork.race-all -/
theorem withFiber_cancelRace_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (raceId : Nat) (hr : m.race? raceId = none) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.cancelRace raceId) =
      ⟨m, { f with frame := { f.frame with current := Prim.success interp.voidValue } },
        yielding, Outcome.continue_, []⟩ := by
  simp [evaluatePrim.withFiber, hr]

/-! ### §20 (2026-09-07): `forkScoped`'s service read and the parallel close's step -/

/-- The `Scope` service read (`Context.ts:423`, `effect.ts:3929`; §20), `forkScoped`'s
`flatMap(scope, …)` first half: the ambient scope's handle as a value. census: fork.scoped -/
theorem withFiber_ambientScope (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (scope : Nat) (h : interp.ambientScope f.context = some scope) :
    evaluatePrim.withFiber interp m f yielding WithFiberAction.ambientScope =
      ⟨m, { f with frame := { f.frame with current := Prim.success (interp.scopeValue scope) } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber, h]
  try rfl

/-- Without the service the read dies with `missingScope` (`Context.get` throws
`ServiceNotFound`, `Context.ts:423`): the same defect `forkScoped` reported before §20.
census: fork.scoped -/
theorem withFiber_ambientScope_none (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (h : interp.ambientScope f.context = none) :
    evaluatePrim.withFiber interp m f yielding WithFiberAction.ambientScope =
      ⟨m, { f with frame := { f.frame with
          current := Prim.failure (Cause.die interp.missingScope) } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber, h]

theorem forkFinalizers_nil (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : RunFiber ν σ β ε δ ι α χ) :
    forkFinalizers interp m host [] = (m, []) := rfl

/-- The parallel close's forks (`forkUnsafe(parent, finalizer(exit_), true, true, "inherit")`,
`:3820`; §20), one per finalizer in close order: an immediate daemon inheriting the closer's
mask, spawned on the closer and left untracked; the closer is unchanged.
census: scope.close-parallel -/
theorem forkFinalizers_cons (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α)) :
    forkFinalizers interp m host (program :: rest) =
      (let s := spawn interp m host program ⟨true, true, Supervision.MaskMode.inherit⟩
       let t := forkFinalizers interp s.1 host rest
       (t.1, s.2.2 :: t.2)) := rfl

/-- The parallel walk's step (`:3819-3824`, §20): every finalizer forked and run now — the
daemons' evaluations are the commands — then the await yielded on the closer's behalf by
`closeParAwait`. census: scope.close-parallel -/
theorem withFiber_closePar (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (finalizers : List (Prim ν σ β ε δ ι α)) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.closePar finalizers) =
      (let s := forkFinalizers interp m f finalizers
       ⟨s.1, f, yielding, Outcome.commands,
         s.2.map Cmd.evaluate ++ [Cmd.closeParAwait f.id yielding s.2]⟩) := rfl

/-- After the daemons' immediate runs the closer yields `fiberAwaitAll(fibers)` under its
generator frame (`:3823-3826`, §20): the iterator frame named `closeDoneName` is pushed with
the void cursor, the await-all park is installed, and the closer's loop continues.
census: scope.close-merge -/
theorem drive_closeParAwait (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : FiberId) (yielding : Bool) (fibers : List FiberId)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? host = some f) :
    drive interp (fuel + 1) m (Cmd.closeParAwait host yielding fibers :: rest) =
      drive interp fuel
        (m.update { f with frame := { f.frame with
          current := interp.parkCode (ParkKind.awaitAll fibers)
          stack := Prim.iterator interp.closeDoneName interp.voidValue :: f.frame.stack } })
        (Cmd.loop f.id yielding :: rest) := by
  simp [drive, driveState, driveStep, settle, hs, hf]

/-- A close await for a fiber the machine does not hold is skipped. -/
theorem drive_closeParAwait_unknown (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : FiberId) (yielding : Bool) (fibers : List FiberId)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? host = none) :
    drive interp (fuel + 1) m (Cmd.closeParAwait host yielding fibers :: rest) =
      drive interp fuel m rest := by
  simp [drive, driveState, driveStep, hs, hf]

/-- `Async` whose register answers at once (`:1120-1126`): the store is updated, the answer is
the fiber's next primitive, and the resumes the store now owes are drained. census: op.Async -/
theorem evaluatePrim_async_immediate (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (register : ν) (withSignal : Bool) (cancel : Option ν) (state : St)
    (next : Prim ν σ β ε δ ι α)
    (hreg : interp.registerAsync register f.id m.nextToken m.state = (state, some next)) :
    let g : RunFiber ν σ β ε δ ι α χ :=
      { f with frame := { f.frame with current := Prim.async register withSignal cancel } }
    evaluatePrim interp m g yielding =
      ⟨{ m with state := state, nextToken := m.nextToken + 1 },
        { g with frame := { g.frame with current := next } }, yielding, Outcome.continue_,
        [Cmd.drainDue]⟩ := by
  simp only [evaluatePrim, hreg]
  try rfl

/-- `Async` whose register parks (`:1128-1141`): the fiber parks on the fresh guard, and the
`AsyncFinalizer` frame carrying the cancel name is pushed exactly when there is a signal or a
cancel effect, so an interrupt while parked runs the cancel through the frame's `contE`.
census: op.Async -/
theorem evaluatePrim_async_parks (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (register : ν) (withSignal : Bool) (cancel : Option ν) (state : St)
    (hreg : interp.registerAsync register f.id m.nextToken m.state = (state, none)) :
    let g : RunFiber ν σ β ε δ ι α χ :=
      { f with frame := { f.frame with current := Prim.async register withSignal cancel } }
    evaluatePrim interp m g yielding =
      (let token := m.nextToken
       let m := { m with state := state, nextToken := m.nextToken + 1 }
       let g := if withSignal || cancel.isSome then
           { g with frame := { g.frame with
              stack := Prim.asyncFinalizer
                (interp.cancelName (cancel.getD interp.abortName) g.id token) :: g.frame.stack } }
         else g
       let g := g.park ⟨token, none, [], [], Resume.void, false⟩
       ⟨m.emit [RunEvent.parkedOn g.id token], g, yielding, Outcome.parked, []⟩) := by
  simp only [evaluatePrim, hreg]
  try rfl

/-! ## Command equations retaining unfinished work

These are the same command clauses above, with the residual command list retained
for the fuel receipts used by replay and the program agreement proof.
-/

theorem driveState_evaluate_enters (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (hexit : f.exit = none) (hrun : f.running = false) (hpark : f.parked = Parked.notParked) :
    driveState interp (fuel + 1) m (Cmd.evaluate id :: rest) =
      driveState interp fuel
        ((m.update { f with running := true, currentOpCount := 0, parked := Parked.notParked }).emit
          [RunEvent.started id])
        (Cmd.loop id false :: rest) := by
  simp [driveState, driveStep, hs, hf, hexit, hrun, hpark]

theorem driveState_loop_parked (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.parked)
    (hd : (iteration interp m f yielding).fiber.frame.deferredInterrupt = false) :
    driveState interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      driveState interp fuel
        ((iteration interp m f yielding).machine.update
          { (iteration interp m f yielding).fiber with running := false })
        ((iteration interp m f yielding).nested ++ rest) := by
  simp [driveState, driveStep, settle, hs, hf, h, hd]

theorem driveState_loop_continues (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.continue_) :
    driveState interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      driveState interp fuel
        ((iteration interp m f yielding).machine.update (iteration interp m f yielding).fiber)
        ((iteration interp m f yielding).nested ++
          [Cmd.loop id (iteration interp m f yielding).yielding] ++ rest) := by
  simp [driveState, driveStep, settle, hs, hf, h]

theorem driveState_loop_answered (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.answered) :
    driveState interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      driveState interp fuel
        ((iteration interp m f yielding).machine.update (iteration interp m f yielding).fiber)
        ((iteration interp m f yielding).nested ++
          [Cmd.deliver id (iteration interp m f yielding).yielding] ++ rest) := by
  simp [driveState, driveStep, settle, hs, hf, h]

theorem driveState_deliver (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (yielding : Bool)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f) :
    driveState interp (fuel + 1) m (Cmd.deliver id yielding :: rest) =
      driveState interp fuel (settle id rest (evaluatePrim interp m f yielding)).1
        (settle id rest (evaluatePrim interp m f yielding)).2 := by
  simp [driveState, driveStep, hs, hf]

theorem driveState_finish (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (exit : Exit β ε δ ι α)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f) :
    driveState interp (fuel + 1) m (Cmd.finish id exit :: rest) =
      (let r := exitFiber interp m { f with running := false } exit
       driveState interp fuel r.1 (r.2 ++ rest)) := by
  simp [driveState, driveStep, hs, hf]

theorem driveState_resume_guard (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (token : Nat)
    (answer : Prim ν σ β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (ht : m.fiber? id = some t) (hp : t.parked = Parked.withGuard token) :
    driveState interp (fuel + 1) m (Cmd.resume id token answer :: rest) =
      driveState interp fuel
        ((m.update { t with
            parked := Parked.notParked
            pending := t.pending.filter fun p => p.token ≠ token
            frame := { t.frame with current := answer } }).emit [RunEvent.resumedWith id token answer])
        (Cmd.evaluate id :: rest) := by
  simp [driveState, driveStep, hs, ht, hp]

end Effect4.Machine
