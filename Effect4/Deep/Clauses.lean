import Effect4.Deep.Fibers
import Effect4.Context.ContextFamily

/-!
# Deep.Clauses

Owner: the mechanism clauses of the reference machine — one theorem per rc.112 arm,
cited by line as the census rows are, over the machine `Effect4/Deep/Fibers.lean` defines.

These are the witnesses the runtime census joins to (`Effect4Test/Audit/RuntimeCoverage.lean`)
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

namespace Effect4.Deep

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
    (hexit : f.exit = none) (hrun : f.running = false) :
    drive interp (fuel + 1) m (Cmd.evaluate id :: rest) =
      drive interp fuel
        ((m.update { f with running := true, currentOpCount := 0, parked := Parked.notParked }).emit
          [RunEvent.started id])
        (Cmd.loop id false :: rest) := by
  simp [drive, hs, hf, hexit, hrun]

/-- `evaluate` on a fiber that has exited is a no-op (`:600`).
census: rule.budget-per-runloop-entry -/
theorem drive_evaluate_exited (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (hexit : f.exit.isSome = true) :
    drive interp (fuel + 1) m (Cmd.evaluate id :: rest) = drive interp fuel m rest := by
  simp [drive, hs, hf, hexit]

/-- `evaluate` on a running fiber is a no-op (`:601`). census: rule.budget-per-runloop-entry -/
theorem drive_evaluate_running (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ)
    (rest : List (Cmd ν σ β ε δ ι α)) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (hrun : f.running = true) :
    drive interp (fuel + 1) m (Cmd.evaluate id :: rest) = drive interp fuel m rest := by
  simp [drive, hs, hf, hrun]

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

/-- The injection (`:647-652`): the fiber parks behind a fresh resume guard, its current
primitive queued at priority 0 on its own dispatcher, the latch set, the override consumed.
census: rule.budget-per-runloop-entry -/
theorem injectYield_fires (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (hp : f.preventYield = false) (hv : yieldVerdict f = true) :
    ∃ it : Iter ν σ β ε δ ι α χ St, injectYield m f false = some it ∧
      it.yielding = true ∧ it.outcome = Outcome.parked ∧
      it.fiber.parked = Parked.withGuard m.nextToken ∧
      it.fiber.yieldOverride = none ∧
      it.fiber.dispatcher = f.dispatcher.enqueue 0 (Task.resume f.id m.nextToken f.frame.current) ∧
      it.machine.nextToken = m.nextToken + 1 := by
  refine ⟨⟨{ m with nextToken := m.nextToken + 1 }.emit
      [RunEvent.yieldInjected f.id f.currentOpCount, RunEvent.parkedOn f.id m.nextToken],
    ({ f with
        yieldOverride := none
        dispatcher := f.dispatcher.enqueue 0 (Task.resume f.id m.nextToken f.frame.current) }).park
      ⟨m.nextToken, none, [], [], Resume.void, false⟩,
    true, Outcome.parked, []⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [injectYield, hp, hv]
  rfl

/-- The iteration is the top of the loop, the counter, and then the injection when it
fires (`:638-652`). census: rule.budget-per-runloop-entry -/
theorem iteration_injected (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (it : Iter ν σ β ε δ ι α χ St) (h : injectYield m (countOp (runloopTop f)) yielding = some it) :
    iteration interp m f yielding = it := by
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
  unfold stepDecision.fire
  rw [h]

/-- The host's callback (`Scheduler.ts:83-103`, the tape's `fire`): the owner's dispatcher
is drained once and the snapshot runs in order, a start as an `evaluate` and a resume as
a `resume`, each followed by the store's due resumes. census: scheduler.host-loop -/
theorem fire_eq (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) (o : RunFiber ν σ β ε δ ι α χ)
    (h : m.fiber? owner = some o) :
    stepDecision.fire interp fuel m owner =
      (o.dispatcher.drain).1.foldl (fun m task =>
          let m := m.emit [RunEvent.ranTask owner task]
          match task with
          | Task.start child => drive interp fuel m [Cmd.evaluate child, Cmd.drainDue]
          | Task.resume target token answer =>
            drive interp fuel m [Cmd.resume target token answer, Cmd.drainDue])
        (m.update { o with dispatcher := (o.dispatcher.drain).2 }) := by
  unfold stepDecision.fire
  rw [h]
  rfl

/-- `flush` (`Scheduler.ts:238-246`): with no armed dispatcher there is nothing to run.
census: scheduler.flush -/
theorem flushAll_idle (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St)
    (h : (m.fibers.filter fun f => f.dispatcher.armed) = []) :
    stepDecision.flushAll interp fuel (rounds + 1) m = m := by
  simp [stepDecision.flushAll, h]

/-- `flush` runs every armed dispatcher in fiber order and goes round again
(`Scheduler.ts:238-246`). census: scheduler.flush -/
theorem flushAll_round (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St)
    (harmed : ((m.fibers.filter fun f => f.dispatcher.armed).map RunFiber.id).isEmpty = false)
    (hs : m.stuck = none) :
    stepDecision.flushAll interp fuel (rounds + 1) m =
      stepDecision.flushAll interp fuel rounds
        (((m.fibers.filter fun f => f.dispatcher.armed).map RunFiber.id).foldl
          (stepDecision.fire interp fuel) m) := by
  simp only [stepDecision.flushAll, harmed, hs, Option.isSome_none, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]

/-- The two budget references default to `2048` and `false` (`Scheduler.ts:269-272`,
`:295-298`), read off an ambient context the family models; the machine reads them through
`RunInterp.budgetOf`. census: scheduler.max-ops-default -/
theorem budget_defaults (store : Effect4.ContextFamily.ContextStore)
    (h : store.ambient = Option.none) :
    (store.referenceValue .maxOpsBeforeYield).getD 2048 = 2048 ∧
      (((store.referenceValue .preventSchedulerYield).getD 0) != 0) = false :=
  ⟨Effect4.ContextFamily.maxOps_default store h, Effect4.ContextFamily.preventYield_default store h⟩

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
    (h : (iteration interp m f yielding).outcome = Outcome.parked) :
    drive interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      drive interp fuel
        ((iteration interp m f yielding).machine.update
          { (iteration interp m f yielding).fiber with running := false })
        ((iteration interp m f yielding).nested ++ rest) := by
  simp [drive, settle, hs, hf, h]

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
  simp [drive, settle, hs, hf, h]

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
  simp [drive, settle, hs, hf, h]

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
  simp [drive, hs, hf]

/-- The exit path as a command (`:611-628`): the fiber is re-read, its loop is over, and
what `exitFiber` leaves to run precedes a drain of the store's owed resumes unless the fiber
parked on its children. census: fork.child -/
theorem drive_finish (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (exit : Exit β ε δ ι α)
    (f : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (hf : m.fiber? id = some f) :
    drive interp (fuel + 1) m (Cmd.finish id exit :: rest) =
      (let r := exitFiber interp m { f with running := false } exit
       drive interp fuel (r.1.update r.2.1)
         (r.2.2.2 ++ (if r.2.2.1 then [] else [Cmd.drainDue]) ++ rest)) := by
  simp [drive, hs, hf]

/-- The resume guard (`:990-993`, `:1121`): a resume whose token is not the guard the fiber
is parked behind is dropped. census: scheduler.yield-now-resume-guard -/
theorem drive_resume_wrong_token (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (token guard : Nat)
    (answer : Prim ν σ β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (ht : m.fiber? id = some t) (hp : t.parked = Parked.withGuard guard)
    (hne : guard ≠ token) :
    drive interp (fuel + 1) m (Cmd.resume id token answer :: rest) = drive interp fuel m rest := by
  simp [drive, hs, ht, hp, hne]

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
  simp [drive, hs, ht, hp]

/-- A resume on a fiber that is not parked is dropped. census: scheduler.yield-now-resume-guard -/
theorem drive_resume_not_parked (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) (token : Nat)
    (answer : Prim ν σ β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ) (rest : List (Cmd ν σ β ε δ ι α))
    (hs : m.stuck = none) (ht : m.fiber? id = some t) (hp : t.parked = Parked.notParked) :
    drive interp (fuel + 1) m (Cmd.resume id token answer :: rest) = drive interp fuel m rest := by
  simp [drive, hs, ht, hp]

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
  let child := RunFiber.make ⟨m.nextId⟩ program childInterruptible
    (interp.budgetOf parent.context) parent.context
  if options.daemon then child
  else { child with observers := [Observer.untrackChild parent.id] }

/-- `forkUnsafe` (`:5264-5284`): the child takes the next id and is appended to the machine,
the id counter advances, and the parent tracks it unless daemon. census: fork.unsafe -/
theorem spawn_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) :
    spawn interp m parent program options =
      ({ m with fibers := m.fibers ++ [spawnChild interp m parent program options], nextId := m.nextId + 1 }.emit
          [RunEvent.forked parent.id ⟨m.nextId⟩ options.daemon],
        { parent with
          children := (if options.daemon then parent.children else parent.children ++ [⟨m.nextId⟩]) },
        ⟨m.nextId⟩) := rfl

/-- The child's identity, context, mask and observer (`:5264-5284`). census: fork.unsafe -/
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
      (spawnChild interp m parent program options).observers =
        (if options.daemon then [] else [Observer.untrackChild parent.id]) := by
  cases hd : options.daemon <;> cases hm : options.maskMode <;> simp [spawnChild, RunFiber.make, hd, hm]

/-- Only a non-daemon fork joins the parent's children (`:5279-5282`).
census: rule.only-fork-child-tracks -/
theorem spawn_daemon_untracked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (hd : options.daemon = true) :
    (spawn interp m parent program options).2.1.children = parent.children := by
  simp [spawn, hd]

/-- The start is asymmetric (`:5274-5278`): immediately means on the caller's stack, as a
command; deferred means a start task at priority 0 on the parent's dispatcher.
census: rule.start-is-asymmetric -/
theorem start_eq (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (child : FiberId) :
    start m parent child true = (m, parent, [Cmd.evaluate child]) ∧
      start m parent child false =
        (m.emit [RunEvent.scheduledTask parent.id 0 (Task.start child)],
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
    (target : FiberId) (scope key : Nat) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.runIn target scope key) =
      (let r := linkScope interp m Supervision.ScopeMode.fiberRunIn scope key target (some target)
        ReasonAnnotations.empty
       ⟨r.1, { f with frame := { f.frame with current := Prim.success interp.voidValue } }, yielding,
        (match r.1.stuck with
          | some why => Outcome.stuck why
          | none => Outcome.continue_), r.2⟩) := rfl

/-- Linking to a closed scope interrupts the fiber at once (`:5374`, `:5454`).
census: fork.fiber-run-in -/
theorem linkScope_closed (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope key : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (exit : Exit β ε δ ι α) (t : RunFiber ν σ β ε δ ι α χ)
    (hclosed : interp.scopeStatus scope m.state = some (some exit)) (ht : m.fiber? target = some t) :
    linkScope interp m mode scope key target interruptor extra =
      (let r := interruptRecord interp interruptor extra t
       ((m.update r.1).emit [RunEvent.scopeClosedOnLink scope target,
          RunEvent.interruptRecorded interruptor target],
        if r.2 then [Cmd.evaluate target] else [])) := by
  simp [linkScope, hclosed, ht]

/-- An unknown scope halts the machine (M7). census: fork.fiber-run-in -/
theorem linkScope_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope key : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (h : interp.scopeStatus scope m.state = none) :
    linkScope interp m mode scope key target interruptor extra = (m.halt (Stuck.unknownScope scope), []) := by
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
  simp [stepDecision, ht]

/-- `runSyncExitWith` (`:5500-5530`): the root is forked and the sync scheduler flushed; the
root's exit is the answer. census: entry.run-sync-exit-with -/
theorem runSyncExit_exited (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ)
    (exit : Exit β ε δ ι α)
    (h : (((stepDecision interp fuel (runFork interp fuel m program context).1 RunDecision.flush).fiber?
        (runFork interp fuel m program context).2).bind RunFiber.exit) = some exit) :
    (runSyncExit interp fuel m program context).2 = exit := by
  simp [runSyncExit, h]

/-- A root that survives the flush is the `AsyncFiberError` defect (`:6184-6196`).
census: entry.async-fiber-error -/
theorem runSyncExit_survives (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (program : Prim ν σ β ε δ ι α) (context : χ)
    (h : (((stepDecision interp fuel (runFork interp fuel m program context).1 RunDecision.flush).fiber?
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
              acc.2 ++ (if r.2 then [Cmd.evaluate t] else []))) := rfl

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

/-- The children clause of the exit path (`:613-617`): with the middleware installed and
tracked children, every child is interrupted with the parent's id, in child order, the parent
remembers the exit it is finalizing and parks on a countdown over the children, to continue
with the restoring frame of that exit. -/
def exitInterruptChildren (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × Bool × List (Cmd ν σ β ε δ ι α) :=
  let (m, nested) := interruptEach interp f.id (interp.stackAnnotations f.id) f.children (m, [])
  let m := m.emit [RunEvent.childrenInterrupted f.id f.children]
  let f := { f with finalizing := some exit, frame := { f.frame with deferredInterrupt := false } }
  let (m, f, parked) :=
    countdownPark interp m f f.children (Resume.continueWith (interp.restoreName exit))
  (m, f, parked, nested)

/-- The store clause of the exit path (`:619-627`): the exit is stored, the stack, the
children, the parks and the context are cleared, every observer fires in index order, and the
observer list is emptied. -/
def exitStore (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × Bool × List (Cmd ν σ β ε δ ι α) :=
  let f := stored interp f exit
  let m := (m.update f).emit [RunEvent.exited f.id exit]
  let (m, nested) := f.observers.foldl (fireObserver interp f.id exit) (m, [])
  let f := { f with observers := [] }
  (m.update f, f, false, nested)
where
  /-- The fiber as the exit path stores it, before its observers fire. -/
  stored (interp : RunInterp ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
      (exit : Exit β ε δ ι α) : RunFiber ν σ β ε δ ι α χ :=
    { f with
      exit := some exit
      finalizing := none
      frame := { f.frame with stack := [], deferredInterrupt := false }
      children := []
      parked := Parked.notParked
      pending := []
      context := interp.emptyContext }

/-- The exit path is the two clauses, chosen by the middleware, the finalizing flag and the
tracked children (`:611-627`). census: rule.children-interrupted-after-exit -/
theorem exitFiber_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    exitFiber interp m f exit =
      if m.middlewareInstalled && f.finalizing.isNone && !f.children.isEmpty then
        exitInterruptChildren interp m f exit
      else exitStore interp m f exit := rfl

/-- Without the middleware the exit is stored at once: the children survive (`:611`).
census: fork.child -/
theorem exitFiber_no_middleware (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (h : m.middlewareInstalled = false) :
    exitFiber interp m f exit = exitStore interp m f exit := by
  rw [exitFiber_eq]; simp [h]

/-- A fiber with no tracked children stores its exit at once, whatever the middleware: a
daemon child is not tracked (`spawn_daemon_untracked`), so a parent's exit never reaches it
(`:613`). census: fork.detach -/
theorem exitFiber_no_children (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (h : f.children = []) :
    exitFiber interp m f exit = exitStore interp m f exit := by
  rw [exitFiber_eq]; simp [h]

/-- A fiber already finalizing stores the exit it is now given (`:612`): the countdown's
continuation is that exit's restoring frame, and an interrupt that lands while the children
are awaited replaces the body's exit with its own failure. census:
rule.children-interrupted-after-exit -/
theorem exitFiber_finalizing (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit body : Exit β ε δ ι α)
    (h : f.finalizing = some body) :
    exitFiber interp m f exit = exitStore interp m f exit := by
  rw [exitFiber_eq]; simp [h]

/-- With the middleware installed, not finalizing, and tracked children, the children clause
runs (`:613`). census: rule.children-interrupted-after-exit -/
theorem exitFiber_children (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (hm : m.middlewareInstalled = true) (hf : f.finalizing = none)
    (hc : f.children.isEmpty = false) :
    exitFiber interp m f exit = exitInterruptChildren interp m f exit := by
  rw [exitFiber_eq]; simp [hm, hf, hc]

/-- The stored fiber: exit set, stack, children, parks, context and observers cleared
(`:619-627`). census: fork.child -/
theorem exitStore_fiber (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (exitStore interp m f exit).2.1 = { exitStore.stored interp f exit with observers := [] } := rfl

/-- The stored fiber's fields, one by one. census: fork.child -/
theorem exitStore_fields (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (exitStore interp m f exit).2.1.exit = some exit ∧
      (exitStore interp m f exit).2.1.finalizing = none ∧
      (exitStore interp m f exit).2.1.frame.stack = [] ∧
      (exitStore interp m f exit).2.1.children = [] ∧
      (exitStore interp m f exit).2.1.parked = Parked.notParked ∧
      (exitStore interp m f exit).2.1.pending = [] ∧
      (exitStore interp m f exit).2.1.context = interp.emptyContext ∧
      (exitStore interp m f exit).2.1.observers = [] ∧
      (exitStore interp m f exit).2.1.frame.deferredInterrupt = false ∧
      (exitStore interp m f exit).2.2.1 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exit path's commands are what the observers asked for, fired in index order over the
machine that already holds the stored fiber (`:621-623`). census: fork.child -/
theorem exitStore_fires (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (exitStore interp m f exit).2.2.2 =
      (f.observers.foldl (fireObserver interp f.id exit)
        ((m.update (exitStore.stored interp f exit)).emit [RunEvent.exited f.id exit], [])).2 := rfl

/-- The children clause, spelled out: the interrupt fold over exactly the tracked children,
the `childrenInterrupted` event, then the countdown over them with the restoring
continuation. census: rule.children-interrupted-after-exit -/
theorem exitInterruptChildren_eq (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    exitInterruptChildren interp m f exit =
      (let r := interruptEach interp f.id (interp.stackAnnotations f.id) f.children (m, [])
       let p := countdownPark interp (r.1.emit [RunEvent.childrenInterrupted f.id f.children])
         { f with finalizing := some exit, frame := { f.frame with deferredInterrupt := false } }
         f.children (Resume.continueWith (interp.restoreName exit))
       (p.1, p.2.1, p.2.2, r.2)) := rfl

/-- The commands the children clause owes are the interrupt fold's: the children that apply
now, in child order. census: fork.detach -/
theorem exitInterruptChildren_interrupts (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (exitInterruptChildren interp m f exit).2.2.2 =
      (interruptEach interp f.id (interp.stackAnnotations f.id) f.children (m, [])).2 := rfl

/-- A countdown keeps the fiber's finalizing flag, parked or not. -/
theorem countdownPark_finalizing (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId)
    (resumeWith : Resume ν) (failFast : Bool) :
    (countdownPark interp m f targets resumeWith failFast).2.1.finalizing = f.finalizing := by
  simp only [countdownPark]
  rcases countdownWalk { m with nextToken := m.nextToken + 1 } targets [] with
    ⟨exits, _ | ⟨target, remaining⟩⟩ <;> rfl

/-- While the children are awaited the parent remembers the exit it is finalizing (`:615`),
so the second pass through the exit path stores rather than re-interrupts.
census: rule.children-interrupted-after-exit -/
theorem exitInterruptChildren_finalizing (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α) :
    (exitInterruptChildren interp m f exit).2.1.finalizing = some exit := by
  simp only [exitInterruptChildren_eq, countdownPark_finalizing]

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

/-- The settling arm of a race callback (`:1503-1514`, R2-12): the race is marked settled and
the host is resumed on its race guard with `interp.raceSettle live accepted` —
`flatMap(uninterruptible(fiberInterruptAll(live)), () => exit)`, so the host interrupts and
awaits the live entrants itself, under a mask; or the exit alone when none is live. -/
def settleRace (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (acc : List (Cmd ν σ β ε δ ι α)) (raceId : Nat) (race : Race β ε δ ι α)
    (state : Supervision.RaceAllState β ε δ ι α) (accepted : Exit β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α) :=
  let m := m.updateRace { race with settled := true }
  let m := m.emit [RunEvent.raceSettled raceId accepted]
  (m, acc ++ [Cmd.resume race.host race.token (interp.raceSettle state.live accepted)])

/-- The settle resumes the host, and nothing else: no entrant is touched until the host runs
the program it was resumed with (`:1510-1514`). census: fork.race-all -/
theorem settleRace_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (acc : List (Cmd ν σ β ε δ ι α)) (raceId : Nat) (race : Race β ε δ ι α)
    (state : Supervision.RaceAllState β ε δ ι α) (accepted : Exit β ε δ ι α) :
    settleRace interp m acc raceId race state accepted =
      ((m.updateRace { race with settled := true }).emit [RunEvent.raceSettled raceId accepted],
        acc ++ [Cmd.resume race.host race.token (interp.raceSettle state.live accepted)]) := rfl

/-- The first accepted callback settles the race: the frozen bookkeeping accepts, the race was
not yet settled, and the settling arm runs over the updated race. census: fork.race-all -/
theorem fireObserver_raceCallback_settles (interp : RunInterp ν σ β ε δ ι α χ St) (id : FiberId)
    (exit : Exit β ε δ ι α) (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (raceId : Nat) (race : Race β ε δ ι α) (accepted : Exit β ε δ ι α)
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
    (raceId : Nat) (race : Race β ε δ ι α)
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
    (raceId : Nat) (race : Race β ε δ ι α)
    (hr : acc.1.race? raceId = some race)
    (hacc : (Supervision.raceComplete race.state id exit).accepted = none) :
    fireObserver interp id exit acc (Observer.raceCallback raceId) =
      ((acc.1.emit [RunEvent.observerFired id (Observer.raceCallback raceId)]).updateRace
        { race with state := Supervision.raceComplete race.state id exit }, acc.2) := by
  simp only [fireObserver, RunMachine.race?_emit, hr, hacc]

/-- A launch after the race has accepted does not start the entrant: it is interrupted with
the host's id and kept (M8; `raceSkipped`). census: fork.race-all -/
theorem drive_launch_skipped (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (entrant : FiberId)
    (rest : List (Cmd ν σ β ε δ ι α)) (race : Race β ε δ ι α) (accepted : Exit β ε δ ι α)
    (e : RunFiber ν σ β ε δ ι α χ) (hs : m.stuck = none) (hr : m.race? raceId = some race)
    (hacc : race.state.accepted = some accepted) (he : m.fiber? entrant = some e) :
    drive interp (fuel + 1) m (Cmd.launch raceId entrant :: rest) =
      (let r := interruptRecord interp (some race.host) (interp.stackAnnotations race.host) e
       drive interp fuel
         ((m.update r.1).emit [RunEvent.raceSkipped raceId entrant,
           RunEvent.interruptRecorded (some race.host) entrant])
         ((if r.2 then [Cmd.evaluate entrant] else []) ++ rest)) := by
  simp [drive, hs, hr, hacc, he]

/-- A launch before the race has accepted moves the entrant from unstarted to live and
evaluates it: the shared set is the race's live list at that moment. census: fork.race-all -/
theorem drive_launch_runs (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (entrant : FiberId)
    (rest : List (Cmd ν σ β ε δ ι α)) (race : Race β ε δ ι α)
    (hs : m.stuck = none) (hr : m.race? raceId = some race) (hacc : race.state.accepted = none) :
    drive interp (fuel + 1) m (Cmd.launch raceId entrant :: rest) =
      drive interp fuel
        ((m.updateRace { race with state :=
            { race.state with
              unstarted := race.state.unstarted.filter fun e => e ≠ entrant
              live := race.state.live ++ [entrant] } }).emit [RunEvent.raceLaunched raceId entrant])
        (Cmd.evaluate entrant :: rest) := by
  simp [drive, hs, hr, hacc]

/-- `fork` (`:5264-5284`): a non-daemon fork installs the interrupt-children middleware
(`forkChild`, `:5253`), then spawn with the options as given, start by `startImmediately`, and
answer the child's handle. census: fork.child -/
theorem withFiber_fork (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.fork program options) =
      (let m' := if options.daemon then m else { m with middlewareInstalled := true }
       let s := spawn interp m' f program options
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_, t.2.2⟩) := rfl

/-- `forkIn` (`:5364-5378`): the child is a daemon of its parent, linked to the supplied
scope by number with the parent as interruptor and the parent's stack annotations, then
started. census: fork.in -/
theorem withFiber_forkIn (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (scope key : Nat) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkIn program options scope key) =
      (let s := spawn interp m f program { options with daemon := true }
       let l := linkScope interp s.1 Supervision.ScopeMode.forkIn scope key s.2.2 (some s.2.1.id)
         (interp.stackAnnotations s.2.1.id)
       let t := start l.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding,
        (match t.1.stuck with
          | some why => Outcome.stuck why
          | none => Outcome.continue_),
        l.2 ++ t.2.2⟩) := rfl

/-- `forkScoped` (`:5400-5406`) resolves the ambient `Scope` service of the parent's context
and is then `forkIn` on it. census: fork.scoped -/
theorem withFiber_forkScoped_ambient (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (key scope : Nat)
    (h : interp.ambientScope f.context = some scope) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options key) =
      (let s := spawn interp m f program { options with daemon := true }
       let l := linkScope interp s.1 Supervision.ScopeMode.forkIn scope key s.2.2 (some s.2.1.id)
         (interp.stackAnnotations s.2.1.id)
       let t := start l.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding,
        (match t.1.stuck with
          | some why => Outcome.stuck why
          | none => Outcome.continue_),
        l.2 ++ t.2.2⟩) := by
  simp only [evaluatePrim.withFiber, h]
  try rfl

/-- Without an ambient `Scope` service `forkScoped` dies with the `missingScope` defect: the
service is required (`:5400`, `Context.get` throws `ServiceNotFound`); it is not the
"unimplemented step" defect (finding S1-1, 2026-09-04). census: fork.scoped -/
theorem withFiber_forkScoped_none (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (key : Nat)
    (h : interp.ambientScope f.context = none) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options key) =
      ⟨m, { f with frame := { f.frame with
          current := Prim.failure (Cause.die interp.missingScope) } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber, h]

/-- Linking to an open scope registers the keyed finalizer in the store and the key-dropping
observer on the fiber (`:5369-5372`, `:5458`). census: fork.in -/
theorem linkScope_open (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope key : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α) (state : St)
    (t : RunFiber ν σ β ε δ ι α χ)
    (hopen : interp.scopeStatus scope m.state = some none)
    (ht : m.fiber? target = some t) (hlive : t.exit = none)
    (hlink : interp.scopeLinkFiber mode scope key target m.state = some state) :
    linkScope interp m mode scope key target interruptor extra =
      (RunMachine.emit
        (RunMachine.modify { m with state := state } target fun t =>
          { t with observers := t.observers ++ [Observer.dropScopeFinalizer scope key] })
        [RunEvent.scopeLinked mode scope key target], []) := by
  simp [linkScope, hopen, ht, hlive, hlink]

/-- An exited fiber is not linked (`:5367`, `:5451-5452`; R2-9). census: fork.fiber-run-in -/
theorem linkScope_open_exited (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope key : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations α)
    (t : RunFiber ν σ β ε δ ι α χ) (exit : Exit β ε δ ι α)
    (hopen : interp.scopeStatus scope m.state = some none)
    (ht : m.fiber? target = some t) (hexited : t.exit = some exit) :
    linkScope interp m mode scope key target interruptor extra = (m, []) := by
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

/-- `fiberInterrupt` (`:859`): record with the caller as interruptor, then await the target.
census: fork.interrupt -/
theorem withFiber_interrupt (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interrupt target) =
      evaluatePrim.interruptThenJoin interp m f yielding target (some f.id) := rfl

/-- Interrupting oneself through the scoped entry is a void no-op (`:868`).
census: fork.interrupt -/
theorem withFiber_interruptScoped_self (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptScoped f.id) =
      ⟨m, { f with frame := { f.frame with current := Prim.success interp.voidValue } },
        yielding, Outcome.continue_, []⟩ := by
  simp [evaluatePrim.withFiber]

/-- Any other target through the scoped entry is the plain interrupt-then-await.
census: fork.interrupt -/
theorem withFiber_interruptScoped_other (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) (h : target ≠ f.id) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptScoped target) =
      evaluatePrim.interruptThenJoin interp m f yielding target (some f.id) := by
  simp [evaluatePrim.withFiber, h]

/-- The request is delivered synchronously (the record, and the evaluation it may owe now),
and the caller then awaits the target on a countdown (`:859`, `interrupt` then `await`).
census: fork.interrupt -/
theorem interruptThenJoin_eq (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) (interruptor : Option FiberId) (t : RunFiber ν σ β ε δ ι α χ)
    (ht : m.fiber? target = some t) :
    evaluatePrim.interruptThenJoin interp m f yielding target interruptor =
      (let r := interruptRecord interp interruptor (interp.stackAnnotations f.id) t
       let m := (m.update r.1).emit [RunEvent.interruptRecorded interruptor target]
       let p := countdownPark interp m f [target] Resume.void
       ⟨p.1, p.2.1, yielding, (if p.2.2 then Outcome.parked else Outcome.continue_),
        if r.2 then [Cmd.evaluate target] else []⟩) := by
  simp only [evaluatePrim.interruptThenJoin, ht]
  try rfl

/-- An unknown target is stuck (S3 §5.1). census: fork.interrupt -/
theorem interruptThenJoin_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : FiberId) (interruptor : Option FiberId) (ht : m.fiber? target = none) :
    evaluatePrim.interruptThenJoin interp m f yielding target interruptor =
      ⟨m, f, yielding, Outcome.stuck (Stuck.unknownFiber target), []⟩ := by
  simp [evaluatePrim.interruptThenJoin, ht]

/-- `fiberInterruptAll` (`:5445-5451`): every request in list order with the given
interruptor (the caller by default), then one explicit await over all of them.
census: fork.interrupt-all -/
theorem withFiber_interruptAll (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (targets : List FiberId) (interruptor : Option FiberId) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.interruptAll targets interruptor) =
      (let r := interruptEach interp (interruptor.getD f.id) (interp.stackAnnotations f.id)
         targets (m, [])
       let p := countdownPark interp r.1 f targets Resume.void
       ⟨p.1, p.2.1, yielding,
        (match p.1.stuck with
          | some why => Outcome.stuck why
          | none => if p.2.2 then Outcome.parked else Outcome.continue_),
        r.2⟩) := rfl

/-- One entrant of a `raceAll` (`:5560-5575`): spawned as an immediate daemon that inherits
the host's mask, with the race callback as its observer, and appended to the entrant list. -/
def raceEntrant (interp : RunInterp ν σ β ε δ ι α χ St) (raceId : Nat)
    (acc : RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × List FiberId)
    (program : Prim ν σ β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × List FiberId :=
  let (m, f, child) :=
    spawn interp acc.1 acc.2.1 program ⟨true, true, Supervision.MaskMode.interruptible⟩
  let m := m.modify child fun c =>
    { c with observers := c.observers ++ [Observer.raceCallback raceId] }
  (m, f, acc.2.2 ++ [child])

/-- The entrant's fork options, read off the definition: immediate, daemon, interruptible
(`forkUnsafe(parent, effect, true, true, false)`, `:1521`; R2-10).
census: rule.only-fork-child-tracks -/
theorem raceEntrant_options (interp : RunInterp ν σ β ε δ ι α χ St) (raceId : Nat)
    (acc : RunMachine ν σ β ε δ ι α χ St × RunFiber ν σ β ε δ ι α χ × List FiberId)
    (program : Prim ν σ β ε δ ι α) :
    raceEntrant interp raceId acc program =
      (let s := spawn interp acc.1 acc.2.1 program ⟨true, true, Supervision.MaskMode.interruptible⟩
       (s.1.modify s.2.2 fun c => { c with observers := c.observers ++ [Observer.raceCallback raceId] },
        s.2.1, acc.2.2 ++ [s.2.2])) := rfl

/-- `raceAll` (`:1490-1531`): the entrants exist as fibers before any launch, the race is
recorded with its host and guard, the host pushes the race's cleanup (`fiberInterruptAll(fibers)`,
`:1530`; R2-13) as an `AsyncFinalizer` frame and parks on the guard, and the launches are
commands in entrant order; the empty race stays parked until the host is interrupted.
census: fork.race-all -/
theorem withFiber_raceAll (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (entrants : List (Prim ν σ β ε δ ι α)) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.raceAll entrants) =
      (let raceId := m.nextRace
       let token := m.nextToken
       let m := { m with nextRace := m.nextRace + 1, nextToken := m.nextToken + 1 }
       let e := entrants.foldl (raceEntrant interp raceId) (m, f, [])
       let race : Race β ε δ ι α :=
         ⟨raceId, e.2.1.id, token, Supervision.RaceAllState.initial e.2.2, false⟩
       let m := RunMachine.emit { e.1 with races := e.1.races ++ [race] }
         [RunEvent.raceStarted raceId e.2.1.id e.2.2]
       let h := e.2.1
       let name := interp.cancelName (interp.raceCancelName raceId) h.id token
       let g := ({ h with frame := { h.frame with stack := Prim.asyncFinalizer name :: h.frame.stack } }).park
         ⟨token, none, [], [], Resume.void, false⟩
       ⟨m.emit [RunEvent.parkedOn g.id token], g, yielding, Outcome.parked,
        e.2.2.map (Cmd.launch raceId)⟩) := rfl

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

/-- The race park's cleanup (`fiberInterruptAll(fibers)`, `:1530`; R2-13): the entrants still
live are interrupted with the running fiber's id and stack annotations, and awaited.
census: fork.race-all -/
theorem withFiber_cancelRace (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (raceId : Nat) (race : Race β ε δ ι α) (hr : m.race? raceId = some race) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.cancelRace raceId) =
      (let r := interruptEach interp f.id (interp.stackAnnotations f.id) race.state.live (m, [])
       let p := countdownPark interp r.1 f race.state.live Resume.void
       ⟨p.1, p.2.1, yielding,
        (match p.1.stuck with
          | some why => Outcome.stuck why
          | none => if p.2.2 then Outcome.parked else Outcome.continue_),
        r.2⟩) := by
  simp only [evaluatePrim.withFiber, hr]
  try rfl

/-- A cleanup for a race the machine does not hold answers void. census: fork.race-all -/
theorem withFiber_cancelRace_unknown (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (raceId : Nat) (hr : m.race? raceId = none) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.cancelRace raceId) =
      ⟨m, { f with frame := { f.frame with current := Prim.success interp.voidValue } },
        yielding, Outcome.continue_, []⟩ := by
  simp [evaluatePrim.withFiber, hr]

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

end Effect4.Deep
