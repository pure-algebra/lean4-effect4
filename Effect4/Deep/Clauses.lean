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
      ⟨m.nextToken, none, 0, [], Resume.void, false, []⟩,
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
  simp [drive, hs, hf, h]

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
  simp [drive, hs, hf, h]

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

/-- A join or await on a live target registers an observer on it and parks behind a fresh
guard (`:5291`, `:5304`, `:565`). census: fork.await -/
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
        g.park ⟨m.nextToken, some target, 0, [], Resume.void, false, []⟩, yielding, Outcome.parked, []⟩ := by
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

end Effect4.Deep
