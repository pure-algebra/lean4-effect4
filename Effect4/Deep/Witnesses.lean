import Effect4.Deep.Stores

/-!
# Deep spike S2: the executable witnesses

Status: design spike, 2026-09-03. Module `Deep.Witnesses` of the non-default `Deep` library;
built with `lake build Deep.Witnesses`. Plan: `docs/research/2026-09-03-deep-plan.md` row S2.
Contract: `docs/research/2026-09-03-fiber-machine-pass-a.md` §1 "Examples". Report:
`docs/research/2026-09-03-spike-s2-stores-witnesses.md`.

Every witness is a program of `Deep.Stores`' declared alphabets, run through
`Effect4.Deep.replayEval` on an explicit decision tape, with the expected exits, traces and
store decided by `decide` or `rfl`. Each witness is a **finite probe** of the machine at one
tape (`AGENTS.md`: a compiling finite probe is reported as a finite probe); none of them states
anything about rc.112 itself. What they check is the four positive Pass A examples and the five
forbidden ones.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Effect4.Deep.Witnesses

open Effect4
open Effect4.Deep

/-! ## Harness -/

abbrev M := RunMachine Name Thunk Val Err Defect FiberId Ann Ctx Stores
abbrev D := RunDecision Name Thunk Val Err Defect FiberId Ann
abbrev Ev := RunEvent Name Thunk Val Err Defect FiberId Ann Ctx

/-- The fuel every witness runs with. Exhaustion is a live frontier (DB-04), never a failure. -/
def fuel : Nat := 400

/-- One root fiber over the empty context, not yet evaluated: the tape owns when it runs, so a
decision such as `installMiddleware` can precede the root's first step. -/
def spawnRoot (m : M) (program : ProgName) (ctx : Ctx) : M :=
  { m with
    fibers := m.fibers ++ [RunFiber.make ⟨m.nextId⟩ (progOf program) true (stores.budgetOf ctx) ctx]
    nextId := m.nextId + 1 }

/-- Replay a tape against one root program over an explicit initial store. All three
`ReplayResult` arms answer the machine; `stuckOf` is how a witness observes the third. -/
def replay (state : Stores) (program : ProgName) (tape : List D) : M :=
  match replayEval stores fuel tape (spawnRoot (RunMachine.empty state) program emptyCtx) with
  | ReplayResult.finished m => m
  | ReplayResult.frontier m => m
  | ReplayResult.stuck _ m => m

/-- The `ReplayResult` arm a tape landed on, as a small code: `0` finished, `1` frontier,
`2` stuck. -/
def replayArm (state : Stores) (program : ProgName) (tape : List D) : Nat :=
  match replayEval stores fuel tape (spawnRoot (RunMachine.empty state) program emptyCtx) with
  | ReplayResult.finished _ => 0
  | ReplayResult.frontier _ => 1
  | ReplayResult.stuck _ _ => 2

/-- Why the machine halted, if it did (M7; S3's stuck marker). -/
def stuckOf (m : M) : Option Stuck := m.stuck

/-- The exit of fiber `id`, if it has one. -/
def exitOf (m : M) (id : Nat) : Option ExitV := (m.fiber? ⟨id⟩).bind RunFiber.exit

/-- The parking state of fiber `id`. -/
def parkedOf (m : M) (id : Nat) : Option Parked := (m.fiber? ⟨id⟩).map RunFiber.parked

/-- The interrupt cause the machine records for `target` interrupted by `who`, with the
caller's annotations on top: `interruptUnsafe` annotates from the target's own stack frame
(`internal/effect.ts:579-580`) and then from the caller's argument (`:582-583`). -/
def interruptedWith (who target : FiberId) (extra : ReasonAnnotations Ann) : ExitV :=
  Exit.failure
    (Cause.annotate
      (Supervision.interruptCause stores.encodeFiber (some who) (stores.stackAnnotations target))
      extra false)

/-- The common case: no caller annotations. -/
def interruptedBy (who target : FiberId) : ExitV :=
  interruptedWith who target ReasonAnnotations.empty

/-- The annotation keys each reason of an exit's cause carries, in order: enough to see *whose*
stack an interrupt was annotated from (M10). -/
def causeKeys : ExitV → List (List String)
  | Exit.success _ => []
  | Exit.failure cause => cause.reasons.map fun reason => reason.annotations.keys

/-! ### Readable codes

`Val` carries a `Cause`, which has no `Repr`; these total codes make a witness readable, and are
themselves decidable, so an assertion over them is as much a theorem as one over the exit. -/

def reasonCode : Reason Err Defect FiberId Ann → Nat
  | Reason.fail Err.boom _ => 100
  | Reason.fail (Err.tag c) _ => 110 + c
  | Reason.die Defect.notImplemented _ => 200
  | Reason.die Defect.asyncFiber _ => 201
  | Reason.die Defect.badName _ => 202
  | Reason.die Defect.missingService _ => 203
  | Reason.die (Defect.user n) _ => 210 + n
  | Reason.interrupt none _ => 300
  | Reason.interrupt (some i) _ => 310 + i.value

def valCode : Val → List Nat
  | Val.unit => [0]
  | Val.nat n => [1, n]
  | Val.bool b => [2, if b then 1 else 0]
  | Val.fiber i => [3, i.value]
  | Val.fibers ids => 4 :: ids.map FiberId.value
  | Val.cell k => [5, k.index]
  | Val.promise k => [6, k.index]
  | Val.scopeHandle s => [7, s]
  | Val.context _ => [8]
  | Val.exitOk v => 9 :: valCode v
  | Val.exitErr c => 10 :: c.reasons.map reasonCode
  | Val.exitNil => [11]
  | Val.exitCons head tail => 12 :: (valCode head ++ valCode tail)

def exitCode : ExitV → List Nat
  | Exit.success v => 0 :: valCode v
  | Exit.failure c => 1 :: c.reasons.map reasonCode

/-- The code of fiber `id`'s exit; `none` is "still live", a frontier. -/
def code (m : M) (id : Nat) : Option (List Nat) := (exitOf m id).map exitCode

/-- How many fibers the machine holds. -/
def fiberCount (m : M) : Nat := m.fibers.length

/-! ### Trace projections -/

/-- Pass A forbidden examples 1 and 5, as one decidable pass over a trace: an observer never
fires before its fiber's `exited` row (`internal/effect.ts:619` precedes `:621`), and no fiber
exits twice (`:600-601`, `:575-577`). -/
def traceWellFormed : List Ev → List FiberId → Bool
  | [], _ => true
  | RunEvent.observerFired f _ :: rest, seen =>
    seen.any (fun g => decide (g = f)) && traceWellFormed rest seen
  | RunEvent.exited f _ :: rest, seen =>
    !(seen.any (fun g => decide (g = f))) && traceWellFormed rest (seen ++ [f])
  | _ :: rest, seen => traceWellFormed rest seen

/-- Pass A forbidden example 3: `SetInterruptible` evaluated as `current` is the
`defaultEvaluate` defect (`Effect4/Runtime/Runtime.lean:1706-1708`), so no witness fiber may
exit with it. -/
def noNotImplementedDefect (m : M) : Bool :=
  m.fibers.all fun f =>
    match f.exit with
    | some (Exit.failure cause) =>
      !(cause.reasons.any
        (fun r => decide (r = Reason.die Defect.notImplemented ReasonAnnotations.empty)))
    | _ => true

/-- How many `finalizerProgram` rows a fiber contributed: a finalizer runs exactly once. -/
def finalizerRuns (m : M) (id : Nat) : Nat :=
  (m.trace.filter fun
    | RunEvent.finalizerProgram f _ _ => decide (f = ⟨id⟩)
    | _ => false).length

/-- The `interruptRecorded` rows, as (interruptor, target). -/
def interruptRows (m : M) : List (Option Nat × Nat) :=
  m.trace.filterMap fun
    | RunEvent.interruptRecorded who target => some (who.map FiberId.value, target.value)
    | _ => none

/-- The `childrenInterrupted` rows of the exit path (`internal/effect.ts:613-617`). -/
def childrenInterruptedRows (m : M) : List (Nat × List Nat) :=
  m.trace.filterMap fun
    | RunEvent.childrenInterrupted parent children =>
      some (parent.value, children.map FiberId.value)
    | _ => none

/-- The `scopeLinked` (`0`) and `scopeClosedOnLink` (`1`) rows. -/
def scopeRows (m : M) : List (List Nat) :=
  m.trace.filterMap fun
    | RunEvent.scopeLinked mode scope key fiber =>
      some [0, (match mode with
        | Supervision.ScopeMode.forkIn => 0
        | Supervision.ScopeMode.fiberRunIn => 1), scope, key, fiber.value]
    | RunEvent.scopeClosedOnLink scope fiber => some [1, scope, fiber.value]
    | _ => none

/-- The `raceLaunched` (`0`), `raceSkipped` (`1`) and `raceSettled` (`2`) rows. -/
def raceRows (m : M) : List (List Nat) :=
  m.trace.filterMap fun
    | RunEvent.raceLaunched race entrant => some [0, race, entrant.value]
    | RunEvent.raceSkipped race entrant => some [1, race, entrant.value]
    | RunEvent.raceSettled race _ => some [2, race]
    | _ => none

/-- The `resumedWith` (`0`) and `exited` (`1`) rows, in trace order: enough to see *when* a
Deferred completion's waiters were resumed relative to the completing fiber's own exit (M1). -/
def resumeAndExitOrder (m : M) : List (List Nat) :=
  m.trace.filterMap fun
    | RunEvent.resumedWith f token _ => some [0, f.value, token]
    | RunEvent.exited f _ => some [1, f.value]
    | _ => none

/-- The `callback` rows of a runtime entry (`runCallbackWith`, `:5470-5490`). -/
def callbackRows (m : M) : List (Nat × List Nat) :=
  m.trace.filterMap fun
    | RunEvent.callback key exit => some (key, exitCode exit)
    | _ => none

/-- Whether a fiber's dispatcher is armed (`Scheduler.ts:207-212`). -/
def armedOf (m : M) (id : Nat) : Option Bool := (m.fiber? ⟨id⟩).map fun f => f.dispatcher.armed

/-- How many tasks are queued on a fiber's dispatcher. -/
def queuedOf (m : M) (id : Nat) : Option Nat :=
  (m.fiber? ⟨id⟩).map fun f => ((f.dispatcher.buckets.map Bucket.tasks).flatten).length

/-- The scope's registered finalizer keys. -/
def scopeKeys (m : M) (key : Nat) : Option (List Nat) :=
  (m.state.scopes.entryAt key).map fun e => e.scope.finalizerKeys

/-- Whether a scope has closed. -/
def scopeClosed (m : M) (key : Nat) : Option Bool :=
  (m.state.scopes.entryAt key).map fun e => e.scope.isClosed

/-! ## Shared fork options -/

/-- `forkUnsafe(parent, self, true, false, "inherit")` (`internal/effect.ts:5264-5272`). -/
def immediateChild : Supervision.ForkOptions := ⟨true, false, Supervision.MaskMode.inherit⟩

/-- The same, deferred onto the parent's dispatcher (`:5277`). -/
def deferredChild : Supervision.ForkOptions := ⟨false, false, Supervision.MaskMode.inherit⟩

/-- `forkIn`'s daemon child (`:5366`). -/
def scopedChild : Supervision.ForkOptions := ⟨true, true, Supervision.MaskMode.inherit⟩

/-- `forkDaemon`'s child (`forkDetach`, `:5288-5294`): immediate, untracked, and — since a
non-daemon `fork` latches the interrupt-children middleware for the process (R2-6, `:5253`) —
the only child that outlives its parent's exit. -/
def daemonChild : Supervision.ForkOptions := ⟨true, true, Supervision.MaskMode.inherit⟩

/-! ## W1 — fork and join

Pass A positive example 1. A parent forks a child, the child runs to its exit, the parent joins
and receives it. -/

/-- Deferred start: the child's start is a task on the parent's dispatcher, run by the tape's
`fire`. -/
def w1DeferredJoin : M :=
  replay Stores.empty
    (ProgName.forkThen (ProgName.value (Val.nat 42)) deferredChild
      Supervision.ObserverMode.joinEffect)
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

/-- Immediate start: the child runs on the parent's stack, so the join finds it already
exited (`:561-562`). -/
def w1ImmediateJoin : M :=
  replay Stores.empty
    (ProgName.forkThen (ProgName.value (Val.nat 42)) immediateChild
      Supervision.ObserverMode.joinEffect)
    [RunDecision.evaluate ⟨0⟩]

/-- `await`: the child's exit is a *value* (`:5304`), so a failing child does not fail the
parent. -/
def w1AwaitFailing : M :=
  replay Stores.empty
    (ProgName.forkThen (ProgName.failCause (Cause.fail (Err.tag 7))) immediateChild
      Supervision.ObserverMode.awaitValue)
    [RunDecision.evaluate ⟨0⟩]

/-- `join`: the child's exit is an *effect* (`:5291`), so a failing child fails the parent. -/
def w1JoinFailing : M :=
  replay Stores.empty
    (ProgName.forkThen (ProgName.failCause (Cause.fail (Err.tag 7))) immediateChild
      Supervision.ObserverMode.joinEffect)
    [RunDecision.evaluate ⟨0⟩]

/-- Tape `[evaluate 0, fire 0]`: the parent exits with the joined child's success. -/
theorem w1_deferred_join_parent : exitOf w1DeferredJoin 0 = some (Exit.success (Val.nat 42)) := by
  decide

/-- The child exits with `42` and the machine holds exactly the two fibers. -/
theorem w1_deferred_join_child :
    exitOf w1DeferredJoin 1 = some (Exit.success (Val.nat 42)) ∧ fiberCount w1DeferredJoin = 2 := by
  decide

/-- The deferred start is a `Task.start` on the *parent's* dispatcher (`:5277`), so before the
tape fires it the child has not run. -/
theorem w1_deferred_start_is_a_task :
    exitOf (replay Stores.empty
      (ProgName.forkThen (ProgName.value (Val.nat 42)) deferredChild
        Supervision.ObserverMode.joinEffect) [RunDecision.evaluate ⟨0⟩]) 1 = none ∧
    armedOf (replay Stores.empty
      (ProgName.forkThen (ProgName.value (Val.nat 42)) deferredChild
        Supervision.ObserverMode.joinEffect) [RunDecision.evaluate ⟨0⟩]) 0 = some true := by
  decide

/-- Tape `[evaluate 0]` with an immediate start: the same exits, with no `fire`. -/
theorem w1_immediate_join :
    exitOf w1ImmediateJoin 0 = some (Exit.success (Val.nat 42)) ∧
      exitOf w1ImmediateJoin 1 = some (Exit.success (Val.nat 42)) := by
  decide

/-- `await` answers the exit as a value: the parent *succeeds* with the child's failed exit. -/
theorem w1_await_is_a_value :
    exitOf w1AwaitFailing 0 =
      some (Exit.success (Val.exitErr (Cause.fail (Err.tag 7)))) := by
  decide

/-- `join` answers the exit as an effect: the parent *fails* with the child's cause. -/
theorem w1_join_is_an_effect :
    exitOf w1JoinFailing 0 = some (Exit.failure (Cause.fail (Err.tag 7))) := by
  decide

/-! ## W2 — masked interrupt

Pass A positive example 2. `onExit`'s `contAll` masks the fiber and pushes the restoring
`SetInterruptible true` frame while the finalizer program runs
(`Effect4/Runtime/Runtime.lean:560-565`, rc.112 `internal/effect.ts:4021`, `:4312-4319`). An
interrupt arriving in that window is recorded and not applied, and is delivered by the unmask
frame's `contAll` when the finalizer's exit passes it. -/

/-- The child: a body that succeeds, and a finalizer that parks. -/
def w2Child : ProgName :=
  ProgName.onExitOf (ProgName.value (Val.nat 7)) (FinName.parkThen 1) false

/-- Tape: evaluate the root (which forks the child as a daemon, so the root's exit leaves it;
the child's finalizer parks), interrupt the masked child, then answer its async. -/
def w2 : M :=
  replay Stores.empty (ProgName.forkOnly w2Child daemonChild)
    [RunDecision.evaluate ⟨0⟩,
      RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩,
      RunDecision.answerAsync ⟨1⟩ 0 (Prim.success Val.unit)]

/-- The cause is recorded against the masked child and, when the finalizer's exit passes the
unmask frame, delivered: the child exits with the interrupt cause carrying the interruptor. -/
theorem w2_delivered_at_unmask : exitOf w2 1 = some (interruptedBy ⟨0⟩ ⟨1⟩) := by decide

/-- The interrupt is *recorded* (one row) and never applied while the fiber is masked: the
child's body still produced its value and the fiber ran on. -/
theorem w2_recorded_once : interruptRows w2 = [(some 0, 1)] := by decide

/-- The finalizer of the `onExit` inside the mask ran exactly once. -/
theorem w2_finalizer_runs_once : finalizerRuns w2 1 = 1 := by decide

/-- Before the async is answered the child is parked, not exited: the interrupt was deferred to
the unmask frame rather than applied at the interrupt. -/
theorem w2_masked_interrupt_does_not_apply :
    exitOf (replay Stores.empty (ProgName.forkOnly w2Child daemonChild)
      [RunDecision.evaluate ⟨0⟩, RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩]) 1 = none := by
  decide

/-! ## W3 — `raceAll`

Pass A positive example 3, plus the three host traces under `test/fixtures/traces/fiber-m3/`. -/

def w3EmptyPending : M :=
  replay Stores.empty (ProgName.raceOf RaceName.empty) [RunDecision.evaluate ⟨0⟩]

def w3EmptyInterrupted : M :=
  replay Stores.empty (ProgName.raceOf RaceName.empty)
    [RunDecision.evaluate ⟨0⟩, RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨0⟩]

def w3StopsLaunch : M :=
  replay Stores.empty (ProgName.raceOf RaceName.successThenSecond) [RunDecision.evaluate ⟨0⟩]

def w3NextLaunch : M :=
  replay Stores.empty (ProgName.raceOf RaceName.failThenSuccess) [RunDecision.evaluate ⟨0⟩]

def w3AllFail : M :=
  replay Stores.empty (ProgName.raceOf RaceName.failThenFail) [RunDecision.evaluate ⟨0⟩]

/-- `test/fixtures/traces/fiber-m3/emptyRacePendingUntilInterrupted.tsv`: the empty race is a live
frontier — the host stays parked on its race token and the machine holds only that fiber. -/
theorem w3_empty_is_a_frontier :
    exitOf w3EmptyPending 0 = none ∧ parkedOf w3EmptyPending 0 = some (Parked.withGuard 0) ∧
      fiberCount w3EmptyPending = 1 := by
  decide

/-- The same race ends only when the host is interrupted. -/
theorem w3_empty_until_interrupted :
    exitOf w3EmptyInterrupted 0 = some (interruptedBy ⟨0⟩ ⟨0⟩) := by decide

/-- `test/fixtures/traces/fiber-m3/raceImmediateSuccessStopsLaunch.tsv`: the first entrant's success
settles the race, and the second entrant is never launched (row `1` is `raceSkipped`). Since M8
the unlaunched entrant is *interrupted with the host's id and kept*, as the golden's
`op interrupt 1` row and `Supervision.RaceAllState` both have it — not deleted; since R2-5 the
interrupt carries the host's stack annotations, as every `fiberInterruptAll` does (`:892-895`).
R2-11 (the entrant is never created in rc.112) is owed to repair step 4. -/
theorem w3_immediate_success_stops_launch :
    exitOf w3StopsLaunch 0 = some (Exit.success (Val.nat 1)) ∧
      raceRows w3StopsLaunch = [[0, 0, 1], [2, 0], [1, 0, 2]] ∧
      fiberCount w3StopsLaunch = 3 ∧
      interruptRows w3StopsLaunch = [(some 0, 2)] ∧
      exitOf w3StopsLaunch 2 =
        some (interruptedWith ⟨0⟩ ⟨2⟩ (stores.stackAnnotations ⟨0⟩)) := by
  decide

/-- `test/fixtures/traces/fiber-m3/raceFailureAllowsNextLaunch.tsv`: a failure does not settle the
race, so the next entrant is launched and its success wins. -/
theorem w3_failure_allows_next_launch :
    exitOf w3NextLaunch 0 = some (Exit.success (Val.nat 9)) ∧
      raceRows w3NextLaunch = [[0, 0, 1], [0, 0, 2], [2, 0]] := by
  decide

/-- `test/fixtures/traces/fiber-m3/raceAllFailuresRetainOrder.tsv`: an all-failed race fails with the
retained causes, in launch order. -/
theorem w3_all_failures_retain_order :
    exitOf w3AllFail 0 =
      some (Exit.failure ⟨[Reason.fail (Err.tag 1) ReasonAnnotations.empty,
        Reason.fail (Err.tag 2) ReasonAnnotations.empty]⟩) := by
  decide

/-! ## W4 — a sibling completes a Deferred

Pass A positive example 4, and the tenth host assertion the sequential projection refused. -/

/-- One pending Deferred, key `0`. -/
def oneCell : Stores := { Stores.empty with deferreds := ⟨[⟨none, []⟩], []⟩ }

/-- The parent forks A (which awaits the Deferred) and B (which completes it with `7`). -/
def w4Sibling : M :=
  replay oneCell
    (ProgName.seqOf
      (ProgName.forkOnly (ProgName.awaitDeferred ⟨0⟩) immediateChild)
      (ProgName.forkOnly
        (ProgName.syncOp (SyncOp.deferredCompleteWith ⟨0⟩
          (Completion.ofExit (Exit.success (Val.nat 7))))) immediateChild))
    [RunDecision.evaluate ⟨0⟩]

/-- Two completions in a row. -/
def w4CompleteTwice : M :=
  replay oneCell
    (ProgName.seqOf
      (ProgName.syncOp (SyncOp.deferredCompleteWith ⟨0⟩
        (Completion.ofExit (Exit.success (Val.nat 7)))))
      (ProgName.syncOp (SyncOp.deferredCompleteWith ⟨0⟩
        (Completion.ofExit (Exit.success (Val.nat 8))))))
    [RunDecision.evaluate ⟨0⟩]

/-- The same, with B doing something *after* the completion, so the completing `sync` is not
the fiber's last primitive. M1 made a stateful `sync` drain the resumes it owes on the spot, so
here A resumes before B's own exit; when the completion is the last primitive the exit path
still runs first (see the report, M1's residual). -/
def w4SiblingThenMore : M :=
  replay oneCell
    (ProgName.seqOf
      (ProgName.forkOnly (ProgName.awaitDeferred ⟨0⟩) immediateChild)
      (ProgName.forkOnly
        (ProgName.seqOf
          (ProgName.syncOp (SyncOp.deferredCompleteWith ⟨0⟩
            (Completion.ofExit (Exit.success (Val.nat 7)))))
          (ProgName.value Val.unit)) immediateChild))
    [RunDecision.evaluate ⟨0⟩]

/-- The parent forks A (awaiting) and B (which runs `Deferred.interrupt`). -/
def w4InterruptWaiter : M :=
  replay oneCell
    (ProgName.seqOf
      (ProgName.forkOnly (ProgName.awaitDeferred ⟨0⟩) immediateChild)
      (ProgName.forkOnly (ProgName.interruptDeferred ⟨0⟩) immediateChild))
    [RunDecision.evaluate ⟨0⟩]

/-- A is resumed with the stored `7` on the same tape decision as B's completion, and B's
completion attempt answered `true`. -/
theorem w4_sibling_resumes :
    exitOf w4Sibling 1 = some (Exit.success (Val.nat 7)) ∧
      exitOf w4Sibling 2 = some (Exit.success (Val.bool true)) ∧
      exitOf w4Sibling 0 = some (Exit.success (Val.fiber ⟨2⟩)) := by
  decide

/-- M1: a completing `sync` resumes the waiters it owes *inside* the completion, on the
completing fiber's own stack, as `Deferred.ts:1655-1659` does — whether or not the completion is
that fiber's last primitive. `resumedWith 1` precedes `exited 2` in both shapes. -/
theorem w4_completion_resumes_on_the_spot :
    resumeAndExitOrder w4SiblingThenMore = [[0, 1, 0], [1, 1], [1, 2], [1, 0]] ∧
      exitOf w4SiblingThenMore 1 = some (Exit.success (Val.nat 7)) ∧
      resumeAndExitOrder w4Sibling = [[0, 1, 0], [1, 1], [1, 2], [1, 0]] := by
  decide

/-- `deferred.single-completion`: the second completion answers `false` and changes nothing. -/
theorem w4_complete_twice_answers_false :
    exitOf w4CompleteTwice 0 = some (Exit.success (Val.bool false)) := by decide

/-- `deferred.interrupt`: the recorded interruptor is the *completing* fiber (`2`), not the
awaiting one, and the waiter is resumed with an interrupt cause. -/
theorem w4_interrupt_reaches_the_waiter :
    exitOf w4InterruptWaiter 1 =
      some (Exit.failure (Cause.interrupt (some ⟨2⟩))) ∧
      exitOf w4InterruptWaiter 2 = some (Exit.success (Val.bool true)) := by
  decide

/-! ## W5 — children after the parent's exit, and `awaitAllChildren` -/

/-- A parent that forks one parked tracked child and then returns. -/
def w5Program : ProgName :=
  ProgName.seqOf (ProgName.forkOnly (ProgName.park 1) immediateChild)
    (ProgName.value Val.unit)

def w5WithMiddleware : M :=
  replay Stores.empty w5Program [RunDecision.installMiddleware, RunDecision.evaluate ⟨0⟩]

/-- The same program with nothing on the tape but the root's start: the `fork` itself latches
the middleware (R2-6). -/
def w5ForkLatches : M :=
  replay Stores.empty w5Program [RunDecision.evaluate ⟨0⟩]

/-- A parent that forks one parked *daemon* child and then returns
(the host golden `daemonSurvivesParentExit`). -/
def w5Daemon : M :=
  replay Stores.empty
    (ProgName.seqOf (ProgName.forkOnly (ProgName.park 1) daemonChild)
      (ProgName.value Val.unit))
    [RunDecision.evaluate ⟨0⟩]

/-- `awaitAllChildren` around a body that forks a second child: only the child added during the
body is awaited (`internal/effect.ts:5318-5322`). -/
def w5AwaitAllChildren : M :=
  replay Stores.empty
    (ProgName.seqOf (ProgName.forkOnly (ProgName.park 1) immediateChild)
      (ProgName.awaitAllNew (ProgName.forkOnly (ProgName.value (Val.nat 5)) deferredChild)))
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

/-- With the middleware latched, the parent's exit interrupts its tracked children with the
parent's id and the parent's stack annotations (`fiberInterruptAll`, `:892-895`; R2-5), and
awaits them before the exit is stored (`:613-617`). -/
theorem w5_middleware_interrupts_children :
    exitOf w5WithMiddleware 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) ∧
      childrenInterruptedRows w5WithMiddleware = [(0, [1])] ∧
      interruptRows w5WithMiddleware = [(some 0, 1)] ∧
      exitOf w5WithMiddleware 0 = some (Exit.success Val.unit) := by
  decide

/-- R2-6: a non-daemon `fork` is `forkChild`, which installs the middleware
(`interruptChildrenPatch()`, `:5253`); the tape's `installMiddleware` changes nothing. -/
theorem w5_fork_latches_the_middleware :
    w5ForkLatches.middlewareInstalled = true ∧
      exitOf w5ForkLatches 1 = exitOf w5WithMiddleware 1 ∧
      childrenInterruptedRows w5ForkLatches = [(0, [1])] ∧
      interruptRows w5ForkLatches = [(some 0, 1)] ∧
      exitOf w5ForkLatches 0 = some (Exit.success Val.unit) := by
  decide

/-- A daemon child is not tracked (`forkDetach`, `:5288-5294`) and does not latch the
middleware: it survives the parent's exit (`daemonSurvivesParentExit`). -/
theorem w5_daemon_child_survives_parent_exit :
    w5Daemon.middlewareInstalled = false ∧
      exitOf w5Daemon 1 = none ∧
      childrenInterruptedRows w5Daemon = [] ∧
      interruptRows w5Daemon = [] ∧
      exitOf w5Daemon 0 = some (Exit.success Val.unit) := by
  decide

/-- `awaitAllChildren` awaits only the children added during its body: the pre-existing parked
child `1` is not awaited (the parent exits although `1` never does) — it is then interrupted
by the parent's exit path, as any tracked child is (R2-6). -/
theorem w5_await_all_children_awaits_only_new :
    exitOf w5AwaitAllChildren 2 = some (Exit.success (Val.nat 5)) ∧
      exitOf w5AwaitAllChildren 0 = some (Exit.success Val.unit) ∧
      childrenInterruptedRows w5AwaitAllChildren = [(0, [1])] ∧
      exitOf w5AwaitAllChildren 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) := by
  decide

/-! ## W6 — scope linkage -/

/-- An open scope, key `0`. -/
def openScope : ScopeEntry := ⟨0, Effect4.Scope.make FinalizerStrategy.sequential⟩

/-- A closed scope, key `1`. -/
def closedScope : ScopeEntry :=
  ⟨1, { strategy := FinalizerStrategy.sequential,
        state := ScopeState.closed (Exit.success Val.unit) }⟩

/-- An open scope, key `2`, already carrying the fiber finalizer of the fiber that will close
it: the self-interruptor case of `:5370`. -/
def selfScope : ScopeEntry :=
  ⟨2, (Effect4.Scope.make FinalizerStrategy.sequential :
        ScopeV).addUnsafe 101 (FinName.interruptFiber ⟨0⟩ true)⟩

def scopeState : Stores :=
  { Stores.empty with scopes := ⟨[openScope, closedScope, selfScope]⟩ }

/-- `forkIn` on an open scope registers the keyed finalizer; closing the scope interrupts the
child. -/
def w6LinkThenClose : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkInScope (ProgName.park 1) scopedChild 0 100)
      (ProgName.closeScopeOf 0 (Exit.success Val.unit)))
    [RunDecision.evaluate ⟨0⟩]

/-- `forkIn` on a closed scope interrupts the child immediately with the parent's id
(`:5374`). -/
def w6ClosedScope : M :=
  replay scopeState (ProgName.forkInScope (ProgName.park 1) scopedChild 1 100)
    [RunDecision.evaluate ⟨0⟩]

/-- The child's exit drops the key (`:5372`). -/
def w6DropsKey : M :=
  replay scopeState (ProgName.forkInScope (ProgName.value (Val.nat 3)) scopedChild 0 100)
    [RunDecision.evaluate ⟨0⟩]

/-- Closing a scope whose fiber finalizer names the closing fiber itself: the finalizer is
void (`:5370`, `interruptor === fiber.id ? void_ : fiberInterrupt(fiber)`). -/
def w6SelfInterruptorSkipped : M :=
  replay scopeState (ProgName.closeScopeOf 2 (Exit.success Val.unit))
    [RunDecision.evaluate ⟨0⟩]

/-- On an open scope the linkage row is emitted, the close runs the fiber finalizer, the child
is interrupted by the closer (`fiberInterrupt`, with the closer's stack annotations, `:880-883`;
R2-5), the key is dropped by the child's exit observer, and the scope ends `Closed`. -/
theorem w6_link_then_close :
    scopeRows w6LinkThenClose = [[0, 0, 0, 100, 1]] ∧
      exitOf w6LinkThenClose 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) ∧
      scopeKeys w6LinkThenClose 0 = some [] ∧
      scopeClosed w6LinkThenClose 0 = some true ∧
      exitOf w6LinkThenClose 0 = some (Exit.success Val.unit) := by
  decide

/-- R2-5 (`E4-RUN-CE-030`): the close's `fiberInterrupt` is annotated from the *closer's*
stack (`:880-883`), so the child's cause carries the closer's key on top of its own — the same
two keys `forkIn`'s closed-scope arm leaves (`w6_closed_scope_interrupts_now`), and one more
than a tape interrupt with empty annotations (`w2_delivered_at_unmask`). -/
theorem w6_close_interrupt_carries_closer_annotations :
    (exitOf w6LinkThenClose 1).map causeKeys = some [["stack1", "stack0"]] ∧
      (exitOf w2 1).map causeKeys = some [["stack1"]] := by
  decide

/-- `fiberRunIn` on a closed scope: the *existing* fiber is interrupted with its **own** id and
with no caller annotations (`internal/effect.ts:5454`), which is the half of M10 that `forkIn`
does differently. -/
def w6ClosedRunIn : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkOnly (ProgName.park 1) immediateChild)
      (ProgName.runInScope ⟨1⟩ 1 100))
    [RunDecision.evaluate ⟨0⟩]

/-- On a closed scope `forkIn` interrupts the child at once, with the *parent's* id and — since
M10 — the *parent's* stack annotations on top of the child's own (`:5374`). -/
theorem w6_closed_scope_interrupts_now :
    scopeRows w6ClosedScope = [[1, 1, 1]] ∧
      exitOf w6ClosedScope 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) ∧
      (exitOf w6ClosedScope 1).map causeKeys = some [["stack1", "stack0"]] := by
  decide

/-- M10, the other half: `fiberRunIn` interrupts with the fiber's own id and adds *no* caller
annotations, so the cause carries only the target's own stack key. The two link modes are now
distinguishable, which they were not while `linkScope` derived the annotations itself. -/
theorem w6_runIn_closed_scope_uses_no_caller_annotations :
    scopeRows w6ClosedRunIn = [[1, 1, 1]] ∧
      exitOf w6ClosedRunIn 1 = some (interruptedBy ⟨1⟩ ⟨1⟩) ∧
      (exitOf w6ClosedRunIn 1).map causeKeys = some [["stack1"]] ∧
      exitOf w6ClosedRunIn 0 = some (Exit.success Val.unit) := by
  decide

/-- A child that exits normally drops its scope key. -/
theorem w6_child_exit_drops_key :
    exitOf w6DropsKey 1 = some (Exit.success (Val.nat 3)) ∧
      scopeKeys w6DropsKey 0 = some [] := by
  decide

/-- The self-interruptor is skipped: no interrupt is recorded and the close succeeds. -/
theorem w6_self_interruptor_skipped :
    interruptRows w6SelfInterruptorSkipped = [] ∧
      exitOf w6SelfInterruptorSkipped 0 = some (Exit.success Val.unit) := by
  decide

/-! ## W6b — the two close strategies -/

/-- A sequential scope carrying two finalizers, the second of which fails. -/
def seqScope : ScopeEntry :=
  ⟨3, (((Effect4.Scope.make FinalizerStrategy.sequential : ScopeV).addUnsafe 200
        (FinName.release 1 false)).addUnsafe 201 (FinName.release 2 true))⟩

/-- The same two finalizers under the parallel strategy. -/
def parScope : ScopeEntry :=
  ⟨4, (((Effect4.Scope.make FinalizerStrategy.parallel : ScopeV).addUnsafe 300
        (FinName.release 3 false)).addUnsafe 301 (FinName.release 4 true))⟩

def closeStores : Stores := { Stores.empty with scopes := ⟨[seqScope, parScope]⟩ }

/-- `internal/effect.ts:3813-3818`: LIFO, each finalizer awaited through its own exit, a
failure captured and not thrown, the captured reasons merged at the end (`:3826`). -/
def w6Sequential : M :=
  replay closeStores (ProgName.closeScopeOf 3 (Exit.success Val.unit)) [RunDecision.evaluate ⟨0⟩]

/-- `internal/effect.ts:3819-3826`: immediate daemon forks inheriting the closer's mask,
awaited together, every exit merged. -/
def w6Parallel : M :=
  replay closeStores (ProgName.closeScopeOf 4 (Exit.success Val.unit)) [RunDecision.evaluate ⟨0⟩]

/-- The sequential close runs the finalizers LIFO on the closing fiber (no fork), captures the
failing one's cause instead of throwing it, and answers the merge. -/
theorem w6_sequential_captures_and_merges :
    exitOf w6Sequential 0 =
      some (Exit.failure ⟨[Reason.fail (Err.tag 2) ReasonAnnotations.empty]⟩) ∧
      fiberCount w6Sequential = 1 ∧ scopeClosed w6Sequential 3 = some true := by
  decide

/-- The parallel close forks one immediate daemon per finalizer, awaits them together, and
merges *every* awaited exit — since M6 through `Resume.exitsValue`, not a store side-channel. -/
theorem w6_parallel_forks_and_merges :
    fiberCount w6Parallel = 3 ∧
      exitOf w6Parallel 1 =
        some (Exit.failure ⟨[Reason.fail (Err.tag 4) ReasonAnnotations.empty]⟩) ∧
      exitOf w6Parallel 2 = some (Exit.success Val.unit) ∧
      exitOf w6Parallel 0 =
        some (Exit.failure ⟨[Reason.fail (Err.tag 4) ReasonAnnotations.empty]⟩) ∧
      scopeClosed w6Parallel 4 = some true := by
  decide

/-! ## W10 — a program that masks its own fiber (M2)

`WithFiberAction.setInterruptible body false` is rc.112's `uninterruptible`
(`internal/effect.ts:4302-4310`): it clears the flag and pushes the restoring
`SetInterruptible true` frame. Before M2 no program could do this, so
`deferred.into-uninterruptible`'s mask clause had no carrier. -/

/-- A fiber that masks itself and then parks on an external async. -/
def w10MaskedChild : ProgName := ProgName.maskedPark 1

/-- Tape: fork the masked child as a daemon (so the root's exit leaves it), interrupt it while
masked, then answer its async. -/
def w10Masked : M :=
  replay Stores.empty (ProgName.forkOnly w10MaskedChild daemonChild)
    [RunDecision.evaluate ⟨0⟩,
      RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩,
      RunDecision.answerAsync ⟨1⟩ 0 (Prim.success Val.unit)]

/-- Without the answer the interrupt is recorded and *not* applied: the fiber is still parked,
because it masked itself. -/
def w10MaskedPending : M :=
  replay Stores.empty (ProgName.forkOnly w10MaskedChild daemonChild)
    [RunDecision.evaluate ⟨0⟩,
      RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩]

/-- The mask holds: the interrupt is recorded once, the fiber does not exit while masked, and
the cause is delivered by the restoring frame when the park is answered. -/
theorem w10_program_masks_its_own_fiber :
    exitOf w10MaskedPending 1 = none ∧
      interruptRows w10Masked = [(some 0, 1)] ∧
      exitOf w10Masked 1 = some (interruptedBy ⟨0⟩ ⟨1⟩) := by
  decide

/-- `deferred.into-uninterruptible` on a *failing* body: `into` masks, `restore` unmasks only
the body, the `Exit` frame captures the body's exit, and the Deferred is completed with it —
so an interrupted or failed body still completes the Deferred (`Deferred.ts:1774-1784`). -/
def w10Into : M :=
  replay oneCell
    (ProgName.intoDeferred (ProgName.failCause (Cause.fail Err.boom)) ⟨0⟩)
    [RunDecision.evaluate ⟨0⟩]

/-- `into` answers `true` and stores the body's failed exit as the completion. -/
theorem w10_into_completes_on_failure :
    exitOf w10Into 0 = some (Exit.success (Val.bool true)) ∧
      ((w10Into.state.deferreds.cellAt ⟨0⟩).map DeferredCell.completion) =
        some (some (Prim.failure (Cause.fail Err.boom))) := by
  decide

/-! ## W11 — an interrupted `Async` runs its cancel through the frame's `contE` (M3)

`Deferred.await` is `internalEffect.callback` whose registration returns the splice-out cleanup
(`Deferred.ts:173-186`). Since M3 the run loop pushes
`Prim.asyncFinalizer (cancelName (cancelAwait cell) fiber token)` at park time, and the frame's
`contE` runs `cancelThenFail` when the failure passes through it
(`internal/effect.ts:1145-1160`). -/

/-- A daemon child (the root's exit leaves it; R2-6) parked on `Deferred.await`, not yet
interrupted. -/
def w11Parked : M :=
  replay oneCell (ProgName.forkOnly (ProgName.awaitDeferred ⟨0⟩) daemonChild)
    [RunDecision.evaluate ⟨0⟩]

/-- The same child, interrupted while parked. -/
def w11Cancelled : M :=
  replay oneCell (ProgName.forkOnly (ProgName.awaitDeferred ⟨0⟩) daemonChild)
    [RunDecision.evaluate ⟨0⟩,
      RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩]

/-- The waiter list of the Deferred. -/
def waitersOf (m : M) (cell : Nat) : Option (List (FiberId × Nat)) :=
  (m.state.deferreds.cellAt ⟨cell⟩).map DeferredCell.waiters

/-- Parking registers the waiter in registration order; the interrupt runs the cancel effect
through the `AsyncFinalizer` frame, which splices exactly that waiter out, and then re-fails
with the very cause that was passing. -/
theorem w11_cancel_splices_the_waiter :
    waitersOf w11Parked 0 = some [(⟨1⟩, 0)] ∧
      waitersOf w11Cancelled 0 = some [] ∧
      exitOf w11Cancelled 1 = some (interruptedBy ⟨0⟩ ⟨1⟩) := by
  decide

/-! ## W12 — `awaitAll` answers the exits it collected (M6)

`fiberAwaitAll` answers `Array<Exit>` (`internal/effect.ts:779`); before M6 the countdown
discarded them and `awaitAll` resumed with `void`. -/

/-- A parent that forks two children with different exits and then awaits both. -/
def w12AwaitAll : M :=
  replay Stores.empty
    (ProgName.seqOf
      (ProgName.forkOnly (ProgName.value (Val.nat 4)) deferredChild)
      (ProgName.seqOf
        (ProgName.forkOnly (ProgName.failCause (Cause.fail (Err.tag 5))) deferredChild)
        (ProgName.awaitFibers [⟨1⟩, ⟨2⟩])))
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

/-- The parent's answer is the two exits, in the order the countdown collected them. -/
theorem w12_awaitAll_answers_the_exits :
    exitOf w12AwaitAll 0 =
      some (Exit.success (stores.exitsValue
        [Exit.success (Val.nat 4),
          Exit.failure (Cause.fail (Err.tag 5))])) := by
  decide

/-! ## W13 — an unknown scope key halts the machine (M7)

`AGENTS.md`: an unanswered choice is a live frontier, never a typed error, cause or refusal.
Before M7 the store had to answer a defect. -/

/-- Closing a scope no allocation minted. -/
def w13UnknownScope : M :=
  replay scopeState (ProgName.closeScopeOf 99 (Exit.success Val.unit)) [RunDecision.evaluate ⟨0⟩]

/-- `forkIn` into a scope no allocation minted. -/
def w13UnknownLink : M :=
  replay scopeState (ProgName.forkInScope (ProgName.park 1) scopedChild 99 100)
    [RunDecision.evaluate ⟨0⟩]

/-- Both halt with `Stuck.unknownScope`, the replay lands on the `stuck` arm, and the fiber
neither fails nor exits: the machine stopped, it did not invent a cause. -/
theorem w13_unknown_scope_is_stuck :
    stuckOf w13UnknownScope = some (Stuck.unknownScope 99) ∧
      exitOf w13UnknownScope 0 = none ∧
      replayArm scopeState (ProgName.closeScopeOf 99 (Exit.success Val.unit))
        [RunDecision.evaluate ⟨0⟩] = 2 := by
  decide

/-- Linking into an unknown scope halts the same way. -/
theorem w13_unknown_link_is_stuck :
    stuckOf w13UnknownLink = some (Stuck.unknownScope 99) ∧
      replayArm scopeState (ProgName.forkInScope (ProgName.park 1) scopedChild 99 100)
        [RunDecision.evaluate ⟨0⟩] = 2 := by
  decide

/-! ## W7 — the `ref.*` quirks on a concrete heap -/

def oneRef : Stores := { Stores.empty with refs := [Val.nat 1] }

def w7Set : M :=
  replay oneRef (ProgName.syncOp (SyncOp.refSet ⟨0⟩ (Val.nat 5))) [RunDecision.evaluate ⟨0⟩]

def w7Update : M :=
  replay oneRef (ProgName.syncOp (SyncOp.refUpdate ⟨0⟩ FnName.incr)) [RunDecision.evaluate ⟨0⟩]

def w7ModifySome : M :=
  replay oneRef (ProgName.syncOp (SyncOp.refModifySome ⟨0⟩ FnName.noChange))
    [RunDecision.evaluate ⟨0⟩]

def w7UpdateSomeAndGet : M :=
  replay { Stores.empty with refs := [Val.nat 3] }
    (ProgName.syncOp (SyncOp.refUpdateSomeAndGet ⟨0⟩ FnName.zeroWhenPositive))
    [RunDecision.evaluate ⟨0⟩]

def w7GetAndUpdateSome : M :=
  replay { Stores.empty with refs := [Val.nat 3] }
    (ProgName.syncOp (SyncOp.refGetAndUpdateSome ⟨0⟩ FnName.zeroWhenPositive))
    [RunDecision.evaluate ⟨0⟩]

/-- `ref.set-void-returns-cell` / `ref.cell-set-returns-self`: the effect succeeds with the
*cell*, and the cell now holds the written value. -/
theorem w7_set_answers_the_cell :
    exitOf w7Set 0 = some (Exit.success (Val.cell ⟨0⟩)) ∧ w7Set.state.refs = [Val.nat 5] := by
  decide

/-- `ref.update`: the same `void`-declared shape succeeds with `undefined`, and the function is
applied exactly once. -/
theorem w7_update_answers_void :
    exitOf w7Update 0 = some (Exit.success Val.unit) ∧ w7Update.state.refs = [Val.nat 2] := by
  decide

/-- `ref.modify-some-no-reread`: on `None` the cell is written back with the value `modify`
already read. -/
theorem w7_modify_some_writes_back_the_read :
    exitOf w7ModifySome 0 = some (Exit.success (Val.nat 1)) ∧
      w7ModifySome.state.refs = [Val.nat 1] := by
  decide

/-- `ref.update-some-and-get-reread`: `updateSomeAndGet` answers the fresh read taken *after*
the write, and `getAndUpdateSome` the value read *before* it. -/
theorem w7_update_some_and_get_rereads :
    exitOf w7UpdateSomeAndGet 0 = some (Exit.success (Val.nat 0)) ∧
      exitOf w7GetAndUpdateSome 0 = some (Exit.success (Val.nat 3)) := by
  decide

/-! ## W8 — the runtime entries -/

/-- `runSyncExitWith` (`:5500-5530`) on a program that parks on an external async. -/
def w8SyncExit : ExitV :=
  (runSyncExit stores fuel (RunMachine.empty Stores.empty) (progOf (ProgName.park 1)) emptyCtx).2

/-- The same entry on a program that finishes. -/
def w8SyncValue : ExitV :=
  (runSyncExit stores fuel (RunMachine.empty Stores.empty)
    (progOf (ProgName.value (Val.nat 3))) emptyCtx).2

/-- `runCallbackWith` (`:5470-5490`). -/
def w8Callback : M :=
  (runCallback stores fuel (RunMachine.empty Stores.empty)
    (progOf (ProgName.value (Val.nat 3))) emptyCtx 77).1

/-- `runPromiseWith` rejects with `causeSquash` of the failure cause. -/
def w8Promise : Except (Squashed Err Defect) Val :=
  promiseOutcome (Exit.failure
    (Cause.combine (Cause.fail (Err.tag 4) : CauseV) (Cause.die Defect.badName)))

/-- A root that survives the flush answers the `AsyncFiberError` defect. -/
theorem w8_sync_exit_async_fiber_error :
    w8SyncExit = Exit.failure (Cause.die Defect.asyncFiber) := by decide

/-- A root that finishes answers its exit. -/
theorem w8_sync_exit_value : w8SyncValue = Exit.success (Val.nat 3) := by decide

/-- `runCallback` fires the callback observer with the root's exit under its key. -/
theorem w8_callback_fires : callbackRows w8Callback = [(77, [0, 1, 3])] := by decide

/-- `promiseOutcome` squashes a failure to its first `Fail`, ahead of the defect. -/
theorem w8_promise_squashes : w8Promise = Except.error (Squashed.error (Err.tag 4)) := rfl

/-! ## Forbidden 4 — a task enqueued during a drain

`runTasks` drains the snapshot once (`Scheduler.ts:225-233`), so the resume the first drained
task enqueues waits for the next `fire`. -/

/-- A program that yields twice. -/
def w9TwoYields : ProgName :=
  ProgName.seqOf (ProgName.yieldNow 0)
    (ProgName.seqOf (ProgName.yieldNow 0) (ProgName.value (Val.nat 1)))

def w9AfterOneFire : M :=
  replay Stores.empty w9TwoYields [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

def w9AfterTwoFires : M :=
  replay Stores.empty w9TwoYields
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩, RunDecision.fire ⟨0⟩]

/-! ## The five forbidden examples -/

/-- Forbidden 1 and 5, on every witness trace: no observer fires before its fiber's `exited`
row, and no fiber exits twice. -/
theorem forbidden_observers_and_double_exit :
    traceWellFormed w1DeferredJoin.trace [] = true ∧
      traceWellFormed w2.trace [] = true ∧
      traceWellFormed w3AllFail.trace [] = true ∧
      traceWellFormed w3StopsLaunch.trace [] = true ∧
      traceWellFormed w4Sibling.trace [] = true ∧
      traceWellFormed w4InterruptWaiter.trace [] = true ∧
      traceWellFormed w5WithMiddleware.trace [] = true ∧
      traceWellFormed w5AwaitAllChildren.trace [] = true ∧
      traceWellFormed w6LinkThenClose.trace [] = true ∧
      traceWellFormed w6Parallel.trace [] = true ∧
      traceWellFormed w9AfterTwoFires.trace [] = true ∧
      traceWellFormed w10Masked.trace [] = true ∧
      traceWellFormed w11Cancelled.trace [] = true ∧
      traceWellFormed w12AwaitAll.trace [] = true := by
  decide

/-- Forbidden 2, as a fact about the step function rather than one tape: an interrupt of a
*running* interruptible fiber is never applied; it sets `deferredInterrupt`
(`internal/effect.ts:589-590`), which the run loop reads at the top of the next iteration
(`:639-642`). -/
theorem forbidden_interrupt_while_running (who : Option FiberId)
    (extra : ReasonAnnotations Ann)
    (f : RunFiber Name Thunk Val Err Defect FiberId Ann Ctx)
    (hexit : f.exit = none) (hrunning : f.running = true)
    (hmask : f.frame.interruptible = true) :
    (interruptRecord stores who extra f).2 = false ∧
      (interruptRecord stores who extra f).1.frame.deferredInterrupt = true := by
  simp [interruptRecord, hexit, hrunning, hmask]

/-- Forbidden 3: a `SetInterruptible` frame *evaluated as `current`* is `defaultEvaluate`'s
defect, never a mask change — the mask change is the frame's `contAll` on the way out. -/
theorem forbidden_setInterruptible_as_current (flag : Bool)
    (frame : FrameFiber Name Thunk Val Err Defect FiberId Ann) :
    (FrameFiber.step stores.toPrimInterp { frame with current := Prim.setInterruptible flag }).1 =
      FrameStep.running
        { frame with current := Prim.failure (Cause.die Defect.notImplemented) } := rfl

/-- Forbidden 3, on the witnesses: no witness fiber ever exits with that defect, so no witness
reached the forbidden step. -/
theorem forbidden_no_notImplemented_defect :
    noNotImplementedDefect w1DeferredJoin = true ∧
      noNotImplementedDefect w2 = true ∧
      noNotImplementedDefect w3AllFail = true ∧
      noNotImplementedDefect w4Sibling = true ∧
      noNotImplementedDefect w5WithMiddleware = true ∧
      noNotImplementedDefect w6LinkThenClose = true ∧
      noNotImplementedDefect w9AfterTwoFires = true ∧
      noNotImplementedDefect w10Masked = true ∧
      noNotImplementedDefect w11Cancelled = true ∧
      noNotImplementedDefect w12AwaitAll = true := by
  decide

/-- Forbidden 4. After one `fire` the fiber has not finished: the task the drained resume
enqueued is still queued, and the dispatcher is armed again. -/
theorem forbidden_task_enqueued_during_drain :
    exitOf w9AfterOneFire 0 = none ∧ armedOf w9AfterOneFire 0 = some true ∧
      queuedOf w9AfterOneFire 0 = some 1 := by
  decide

/-- The next `fire` runs it. -/
theorem w9_next_fire_runs_it :
    exitOf w9AfterTwoFires 0 = some (Exit.success (Val.nat 1)) := by decide

/-! ## DB-07: the store is threaded out of a failing step and never restored -/

def dbSevenState : Stores := { Stores.empty with refs := [Val.nat 1] }

/-- A program that writes a Ref and then fails. -/
def dbSeven : M :=
  replay dbSevenState
    (ProgName.seqOf (ProgName.syncOp (SyncOp.refSet ⟨0⟩ (Val.nat 5)))
      (ProgName.failCause (Cause.fail Err.boom)))
    [RunDecision.evaluate ⟨0⟩]

/-- The fiber fails, and the store the machine carries afterwards is the store the failing
fiber had reached — the write is still there, available to finalization
(`AGENTS.md`, DB-07). The general obligation is stated beside the interp in `Deep.Stores`. -/
theorem db07_store_survives_failure :
    exitOf dbSeven 0 = some (Exit.failure (Cause.fail Err.boom)) ∧
      dbSeven.state.refs = [Val.nat 5] := by
  decide



/-! ## Axiom receipt

Checked once with `#print axioms` over the theorems above: every one depends on `propext` and
`Quot.sound` only (`forbidden_setInterruptible_as_current`, which is `rfl`, on `propext`
alone) — the receipt `docs/RUNTIME-COVERAGE.md:52-55` requires of a witness. There is no
`sorry`, no `native_decide` and no custom axiom anywhere in this spike. -/

end Effect4.Deep.Witnesses


