import Effect4.Laws.Auto.Obligations
import Effect4.Machine.Stores

/-!
# Deep spike S2: the executable witnesses

Status: design spike, 2026-09-03. Module `Deep.Witnesses` of the non-default `Deep` library;
built with `lake build Deep.Witnesses`. Plan: `docs/research/2026-09-03-deep-plan.md` row S2.
Contract: `docs/research/2026-09-03-fiber-machine-pass-a.md` §1 "Examples". Report:
`docs/research/2026-09-03-spike-s2-stores-witnesses.md`.

Every witness is a program of `Deep.Stores`' declared alphabets, run through
`Effect4.Machine.replayEval` on an explicit decision tape, with the expected exits, traces and
store decided by `decide` or `rfl`. Each witness is a **finite probe** of the machine at one
tape (`AGENTS.md`: a compiling finite probe is reported as a finite probe); none of them states
anything about rc.112 itself. What they check is the four positive Pass A examples and the five
forbidden ones.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Effect4.Machine.Witnesses

open Effect4
open Effect4.Machine

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
  | ReplayResult.frontier _ m => m
  | ReplayResult.stuck _ m => m

/-- The `ReplayResult` arm a tape landed on, as a small code: `0` finished, `1` frontier,
`2` stuck. -/
def replayArm (state : Stores) (program : ProgName) (tape : List D) : Nat :=
  match replayEval stores fuel tape (spawnRoot (RunMachine.empty state) program emptyCtx) with
  | ReplayResult.finished _ => 0
  | ReplayResult.frontier _ _ => 1
  | ReplayResult.stuck _ _ => 2

/-- Why the machine halted, if it did (M7; S3's stuck marker). -/
def stuckOf (m : M) : Option Stuck := m.stuck

/-- The exit of fiber `id`, if it has one. -/
def exitOf (m : M) (id : Nat) : Option ExitV := (m.fiber? ⟨id⟩).bind RunFiber.exit

/-- The parking state of fiber `id`. -/
def parkedOf (m : M) (id : Nat) : Option Parked := (m.fiber? ⟨id⟩).map RunFiber.parked

/-- The observers registered on fiber `id`. -/
def observersOf (m : M) (id : Nat) : Option (List Observer) := (m.fiber? ⟨id⟩).map RunFiber.observers

/-- The frames on fiber `id`'s stack. -/
def stackOf (m : M) (id : Nat) : Option (List Program) := (m.fiber? ⟨id⟩).map fun f => f.frame.stack

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
  -- the code does not carry the pair; it is read through `causeImage` and the truth wire
  | Reason.fail (Err.tagged _ _) _ => 101
  | Reason.fail (Err.text _) _ => 102
  | Reason.fail (Err.tag c) _ => 110 + c
  | Reason.die Defect.notImplemented _ => 200
  | Reason.die Defect.asyncFiber _ => 201
  | Reason.die Defect.badName _ => 202
  | Reason.die Defect.missingService _ => 203
  | Reason.die (Defect.user n) _ => 210 + n
  -- Diagnostic only: exact payloads are carried by causeImage, not this code.
  | Reason.die (Defect.error _) _ => 220
  | Reason.interrupt none _ => 300
  | Reason.interrupt (some i) _ => 310 + i.value

/-- The reasons of a written cause, coded; a shape no cause wrote codes as nothing. -/
def causeCode (written : Val) : List Nat :=
  ((causeImage.ofVal written).map fun c => c.reasons.map reasonCode).getD []

/-- The fibers of a snapshot's payload; a payload that is not of fiber handles codes as
nothing. -/
def snapshotCode (handles : Val) : List Nat :=
  (((Effect4.Store.Image.list Value.fiberHandle).ofVal handles).map fun ids =>
    ids.map FiberId.value).getD []

mutual
/-- The codes are the ones the old carrier had, arm for arm: a list is `12` per cell and `11`
at its end; a shape the machine never produces (a string, a memo-map handle, …) is `13`. -/
def valCode : Val → List Nat
  | Val.unit => [0]
  | Val.nat n => [1, n]
  | Val.bool b => [2, if b then 1 else 0]
  | Value.fiber i => [3, i]
  | Value.cell k => [5, k]
  | Value.promise k => [6, k]
  | Value.scope s => [7, s]
  | Val.exitOk v => 9 :: valCode v
  | Value.exitErr written => 10 :: causeCode written
  | Value.fiberContext _ _ _ => [8]
  | Value.fiberSnapshot handles => 4 :: snapshotCode handles
  | .list values => valCodeList values
  | _ => [13]
def valCodeList : List Val → List Nat
  | [] => [11]
  | head :: tail => 12 :: (valCode head ++ valCodeList tail)
end

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
`defaultEvaluate` defect (`src/Effect4/Machine/Frames.lean:1706-1708`), so no witness fiber may
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

/-- The exits the `finalizerProgram` rows of fiber `id` carry, in order: what each finalizer
program was handed. -/
def finalizerExits (m : M) (id : Nat) : List ExitV :=
  m.trace.filterMap fun
    | RunEvent.finalizerProgram f _ exit => if f = ⟨id⟩ then some exit else none
    | _ => none

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

/-- The `raceLaunched` (`0`) and `raceSettled` (`2`) rows. (`1` was `raceSkipped`, retired
with R2-11: an unlaunched entrant is never forked, so nothing is skipped.) -/
def raceRows (m : M) : List (List Nat) :=
  m.trace.filterMap fun
    | RunEvent.raceLaunched race entrant => some [0, race, entrant.value]
    | RunEvent.raceSettled race _ => some [2, race]
    | _ => none

/-- How many entrants of race `race` were never forked. -/
def unlaunchedOf (m : M) (race : Nat) : Option Nat := (m.race? race).map fun r => r.programs.length

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

/-- The host callbacks scheduled, in arming order (R2-15). -/
def armedQueueOf (m : M) : List Nat := m.armed.map FiberId.value

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
theorem w1_deferred_join_parent : exitOf w1DeferredJoin 0 = some (Exit.success (Val.nat 42)) :=
  by aesop

/-- The child exits with `42` and the machine holds exactly the two fibers. -/
theorem w1_deferred_join_child :
    exitOf w1DeferredJoin 1 = some (Exit.success (Val.nat 42)) ∧ fiberCount w1DeferredJoin = 2 :=
  by aesop

/-- The deferred start is a `Task.start` on the *parent's* dispatcher (`:5277`), so before the
tape fires it the child has not run. -/
theorem w1_deferred_start_is_a_task :
    exitOf (replay Stores.empty
      (ProgName.forkThen (ProgName.value (Val.nat 42)) deferredChild
        Supervision.ObserverMode.joinEffect) [RunDecision.evaluate ⟨0⟩]) 1 = none ∧
    armedOf (replay Stores.empty
      (ProgName.forkThen (ProgName.value (Val.nat 42)) deferredChild
        Supervision.ObserverMode.joinEffect) [RunDecision.evaluate ⟨0⟩]) 0 = some true :=
  by aesop

/-- Tape `[evaluate 0]` with an immediate start: the same exits, with no `fire`. -/
theorem w1_immediate_join :
    exitOf w1ImmediateJoin 0 = some (Exit.success (Val.nat 42)) ∧
      exitOf w1ImmediateJoin 1 = some (Exit.success (Val.nat 42)) :=
  by aesop

/-- `await` answers the exit as a value: the parent *succeeds* with the child's failed exit. -/
theorem w1_await_is_a_value :
    exitOf w1AwaitFailing 0 =
      some (Exit.success (Val.exitErr (Cause.fail (Err.tag 7)))) :=
  by aesop

/-- `join` answers the exit as an effect: the parent *fails* with the child's cause. -/
theorem w1_join_is_an_effect :
    exitOf w1JoinFailing 0 = some (Exit.failure (Cause.fail (Err.tag 7))) :=
  by aesop

/-! ## W2 — masked interrupt

Pass A positive example 2. `onExit`'s `contAll` masks the fiber and pushes the restoring
`SetInterruptible true` frame while the finalizer program runs
(`src/Effect4/Machine/Frames.lean:560-565`, rc.112 `internal/effect.ts:4021`, `:4312-4319`). An
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
      RunDecision.answerAsync ⟨1⟩ 0 (Completion.ofExit (Exit.success Val.unit))]

/-- The cause is recorded against the masked child and, when the finalizer's exit passes the
unmask frame, delivered: the child exits with the interrupt cause carrying the interruptor. -/
theorem w2_delivered_at_unmask : exitOf w2 1 = some (interruptedBy ⟨0⟩ ⟨1⟩) :=
  by aesop

/-- The interrupt is *recorded* (one row) and never applied while the fiber is masked: the
child's body still produced its value and the fiber ran on. -/
theorem w2_recorded_once : interruptRows w2 = [(some 0, 1)] :=
  by aesop

/-- The finalizer of the `onExit` inside the mask ran exactly once. -/
theorem w2_finalizer_runs_once : finalizerRuns w2 1 = 1 :=
  by aesop

/-- Before the async is answered the child is parked, not exited: the interrupt was deferred to
the unmask frame rather than applied at the interrupt. -/
theorem w2_masked_interrupt_does_not_apply :
    exitOf (replay Stores.empty (ProgName.forkOnly w2Child daemonChild)
      [RunDecision.evaluate ⟨0⟩, RunDecision.interruptFrom (some ⟨0⟩) ReasonAnnotations.empty ⟨1⟩]) 1 = none :=
  by aesop

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

/-- `Test/fixtures/traces/fiber-m3/emptyRacePendingUntilInterrupted.tsv`: the empty race is a live
frontier — the host stays parked on its race token and the machine holds only that fiber. -/
theorem w3_empty_is_a_frontier :
    exitOf w3EmptyPending 0 = none ∧ parkedOf w3EmptyPending 0 = some (Parked.withGuard 0) ∧
      fiberCount w3EmptyPending = 1 :=
  by aesop

/-- The same race ends only when the host is interrupted. -/
theorem w3_empty_until_interrupted :
    exitOf w3EmptyInterrupted 0 = some (interruptedBy ⟨0⟩ ⟨0⟩) :=
  by aesop

/-- `Test/fixtures/traces/fiber-m3/raceImmediateSuccessStopsLaunch.tsv` (host face, `answer
started [0, []]`): the first entrant's success settles the race, and the second entrant is
*never forked* — the register loop breaks once done (`:1527`, R2-11, `E4-RUN-CE-035`): two
fibers exist, one entrant program is left unlaunched, and nothing is interrupted. M8 had kept
a spawned-then-interrupted fiber for it, on the strength of a Lean-face golden. -/
theorem w3_immediate_success_stops_launch :
    exitOf w3StopsLaunch 0 = some (Exit.success (Val.nat 1)) ∧
      raceRows w3StopsLaunch = [[0, 0, 1], [2, 0]] ∧
      fiberCount w3StopsLaunch = 2 ∧
      unlaunchedOf w3StopsLaunch 0 = some 1 ∧
      interruptRows w3StopsLaunch = [] ∧
      exitOf w3StopsLaunch 2 = none :=
  by aesop

/-- `Test/fixtures/traces/fiber-m3/raceFailureAllowsNextLaunch.tsv`: a failure does not settle the
race, so the next entrant is launched and its success wins. -/
theorem w3_failure_allows_next_launch :
    exitOf w3NextLaunch 0 = some (Exit.success (Val.nat 9)) ∧
      raceRows w3NextLaunch = [[0, 0, 1], [0, 0, 2], [2, 0]] :=
  by aesop

/-- `Test/fixtures/traces/fiber-m3/raceAllFailuresRetainOrder.tsv`: an all-failed race fails with the
retained causes, in launch order. -/
theorem w3_all_failures_retain_order :
    exitOf w3AllFail 0 =
      some (Exit.failure ⟨[Reason.fail (Err.tag 1) ReasonAnnotations.empty,
        Reason.fail (Err.tag 2) ReasonAnnotations.empty]⟩) :=
  by aesop

/-! ## W4 — a sibling completes a Deferred

Pass A positive example 4, and the tenth host assertion the sequential projection refused. -/

/-- One pending Deferred, key `0`. -/
def oneCell : Stores := { Stores.empty with deferreds := ⟨[⟨none, WakeList.empty⟩], []⟩ }

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
      exitOf w4Sibling 0 = some (Exit.success (Val.fiber ⟨2⟩)) :=
  by aesop

/-- M1: a completing `sync` resumes the waiters it owes *inside* the completion, on the
completing fiber's own stack, as `Deferred.ts:1655-1659` does — whether or not the completion is
that fiber's last primitive. `resumedWith 1` precedes `exited 2` in both shapes. -/
theorem w4_completion_resumes_on_the_spot :
    resumeAndExitOrder w4SiblingThenMore = [[0, 1, 0], [1, 1], [1, 2], [1, 0]] ∧
      exitOf w4SiblingThenMore 1 = some (Exit.success (Val.nat 7)) ∧
      resumeAndExitOrder w4Sibling = [[0, 1, 0], [1, 1], [1, 2], [1, 0]] :=
  by aesop

/-- `deferred.single-completion`: the second completion answers `false` and changes nothing. -/
theorem w4_complete_twice_answers_false :
    exitOf w4CompleteTwice 0 = some (Exit.success (Val.bool false)) :=
  by aesop

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
      exitOf w5WithMiddleware 0 = some (Exit.success Val.unit) :=
  by aesop

/-- R2-6: a non-daemon `fork` is `forkChild`, which installs the middleware
(`interruptChildrenPatch()`, `:5253`); the tape's `installMiddleware` changes nothing. -/
theorem w5_fork_latches_the_middleware :
    w5ForkLatches.middlewareInstalled = true ∧
      exitOf w5ForkLatches 1 = exitOf w5WithMiddleware 1 ∧
      childrenInterruptedRows w5ForkLatches = [(0, [1])] ∧
      interruptRows w5ForkLatches = [(some 0, 1)] ∧
      exitOf w5ForkLatches 0 = some (Exit.success Val.unit) :=
  by aesop

/-- A daemon child is not tracked (`forkDetach`, `:5288-5294`) and does not latch the
middleware: it survives the parent's exit (`daemonSurvivesParentExit`). -/
theorem w5_daemon_child_survives_parent_exit :
    w5Daemon.middlewareInstalled = false ∧
      exitOf w5Daemon 1 = none ∧
      childrenInterruptedRows w5Daemon = [] ∧
      interruptRows w5Daemon = [] ∧
      exitOf w5Daemon 0 = some (Exit.success Val.unit) :=
  by aesop

/-- `awaitAllChildren` around a body that forks a child and then *fails*: the await is
`onExit`'s finalizer (`:5319-5333`, R2-7, `E4-RUN-CE-037`), so it runs on the failure too —
the parent parks until the child is started and exits, and the child ends by its own exit,
not by the parent's. -/
def w5AwaitAllChildrenFails : M :=
  replay Stores.empty
    (ProgName.awaitAllNew
      (ProgName.seqOf (ProgName.forkOnly (ProgName.value (Val.nat 5)) deferredChild)
        (ProgName.failCause (Cause.fail Err.boom))))
    [RunDecision.evaluate ⟨0⟩]

def w5AwaitAllChildrenFailsFired : M :=
  replay Stores.empty
    (ProgName.awaitAllNew
      (ProgName.seqOf (ProgName.forkOnly (ProgName.value (Val.nat 5)) deferredChild)
        (ProgName.failCause (Cause.fail Err.boom))))
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

theorem w5_await_all_children_on_failure :
    exitOf w5AwaitAllChildrenFails 0 = none ∧
      exitOf w5AwaitAllChildrenFails 1 = none ∧
      parkedOf w5AwaitAllChildrenFails 0 = some (Parked.withGuard 0) ∧
      exitOf w5AwaitAllChildrenFailsFired 1 = some (Exit.success (Val.nat 5)) ∧
      exitOf w5AwaitAllChildrenFailsFired 0 = some (Exit.failure (Cause.fail Err.boom)) ∧
      finalizerRuns w5AwaitAllChildrenFailsFired 0 = 1 :=
  by aesop

/-- `awaitAllChildren` awaits only the children added during its body: the pre-existing parked
child `1` is not awaited (the parent exits although `1` never does) — it is then interrupted
by the parent's exit path, as any tracked child is (R2-6). -/
theorem w5_await_all_children_awaits_only_new :
    exitOf w5AwaitAllChildren 2 = some (Exit.success (Val.nat 5)) ∧
      -- `awaitAllChildren(self)` answers the body's own value (`onExit`, R2-7): the handle
      exitOf w5AwaitAllChildren 0 = some (Exit.success (Val.fiber ⟨2⟩)) ∧
      childrenInterruptedRows w5AwaitAllChildren = [(0, [1])] ∧
      exitOf w5AwaitAllChildren 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) :=
  by aesop

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

/-- The supply is above every registration key the three scopes already hold
(`Stores.ScopeKeysFresh`), which is what makes the next allocated identity fresh. -/
def scopeState : Stores :=
  { Stores.empty with scopes := ⟨[openScope, closedScope, selfScope]⟩, nextName := 102 }

theorem scopeState_keysFresh : scopeState.ScopeKeysFresh := by
  show ∀ e ∈ scopeState.scopes.entries, ∀ k ∈ e.scope.finalizerKeys, k < scopeState.nextName
  decide

/-- `forkIn` on an open scope registers the keyed finalizer; closing the scope interrupts the
child. -/
def w6LinkThenClose : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkInScope (ProgName.park 1) scopedChild 0)
      (ProgName.closeScopeOf 0 (Exit.success Val.unit)))
    [RunDecision.evaluate ⟨0⟩]

/-- `forkIn` on a closed scope interrupts the child immediately with the parent's id
(`:5374`). -/
def w6ClosedScope : M :=
  replay scopeState (ProgName.forkInScope (ProgName.park 1) scopedChild 1)
    [RunDecision.evaluate ⟨0⟩]

/-- The child's exit drops the key (`:5372`). -/
def w6DropsKey : M :=
  replay scopeState (ProgName.forkInScope (ProgName.value (Val.nat 3)) scopedChild 0)
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
    scopeRows w6LinkThenClose = [[0, 0, 0, 102, 1]] ∧
      exitOf w6LinkThenClose 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) ∧
      scopeKeys w6LinkThenClose 0 = some [] ∧
      scopeClosed w6LinkThenClose 0 = some true ∧
      exitOf w6LinkThenClose 0 = some (Exit.success Val.unit) :=
  by aesop

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
      (ProgName.runInScope ⟨1⟩ 1))
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

/-- R2-8 (`E4-RUN-CE-036`): `forkIn` forks and, when immediate, *runs* the child first, and
links only a child that has not exited (`:5366-5376`): an immediately finished child is never
linked — no `scopeLinked` row, no key to drop. -/
theorem w6_child_exit_drops_key :
    exitOf w6DropsKey 1 = some (Exit.success (Val.nat 3)) ∧
      scopeRows w6DropsKey = [] ∧
      scopeKeys w6DropsKey 0 = some [] :=
  by aesop

/-- The same child started on the parent's dispatcher: it has not run when the link happens,
so it is linked; its later exit drops the key. -/
def w6DeferredLinked : M :=
  replay scopeState
    (ProgName.forkInScope (ProgName.value (Val.nat 3)) ⟨false, true, Supervision.MaskMode.inherit⟩ 0)
    [RunDecision.evaluate ⟨0⟩]

def w6DeferredLinkedFired : M :=
  replay scopeState
    (ProgName.forkInScope (ProgName.value (Val.nat 3)) ⟨false, true, Supervision.MaskMode.inherit⟩ 0)
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

theorem w6_deferred_child_is_linked :
    scopeRows w6DeferredLinked = [[0, 0, 0, 102, 1]] ∧
      scopeKeys w6DeferredLinked 0 = some [102] ∧
      exitOf w6DeferredLinked 1 = none ∧
      exitOf w6DeferredLinkedFired 1 = some (Exit.success (Val.nat 3)) ∧
      scopeKeys w6DeferredLinkedFired 0 = some [] :=
  by aesop

/-- The self-interruptor is skipped: no interrupt is recorded and the close succeeds. -/
theorem w6_self_interruptor_skipped :
    interruptRows w6SelfInterruptorSkipped = [] ∧
      exitOf w6SelfInterruptorSkipped 0 = some (Exit.success Val.unit) :=
  by aesop

/-! ### W6a — every executed registration has its own identity (`E4-CHECK-CE-016`)

rc.112 allocates `const key = {}` per registration (`internal/effect.ts:5366-5372`,
`:5457-5460`). These are the ground receipts under the general laws
(`Stores.scopeLinkFiber_allocates`, `_fresh`, `_keysFresh`, `_appends`,
`dropFinalizer_removes_its_own`): the second registration into one scope neither shares the
first's key nor replaces its cleanup obligation. -/

/-- Two `forkIn`s into the same open scope, from one parent. -/
def w6TwoLinks : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkInScope (ProgName.park 1) scopedChild 0)
      (ProgName.forkInScope (ProgName.park 2) scopedChild 0))
    [RunDecision.evaluate ⟨0⟩]

/-- Both children are registered, under two different identities, and both obligations stand.
Under the old scheme the compile point supplied one key for both and the second registration
replaced the first. -/
theorem w6_two_links_have_two_keys :
    scopeRows w6TwoLinks = [[0, 0, 0, 102, 1], [0, 0, 0, 103, 2]] ∧
      scopeKeys w6TwoLinks 0 = some [102, 103] ∧
      exitOf w6TwoLinks 1 = none ∧
      exitOf w6TwoLinks 2 = none :=
  by aesop

/-- Both children are still parked, so closing the scope must interrupt *both*. -/
def w6TwoLinksClosed : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkInScope (ProgName.park 1) scopedChild 0)
      (ProgName.seqOf (ProgName.forkInScope (ProgName.park 2) scopedChild 0)
        (ProgName.closeScopeOf 0 (Exit.success Val.unit))))
    [RunDecision.evaluate ⟨0⟩]

theorem w6_close_interrupts_both_children :
    exitOf w6TwoLinksClosed 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) ∧
      exitOf w6TwoLinksClosed 2 =
        some (interruptedWith ⟨0⟩ ⟨2⟩ (stores.stackAnnotations ⟨0⟩)) ∧
      scopeKeys w6TwoLinksClosed 0 = some [] ∧
      scopeClosed w6TwoLinksClosed 0 = some true :=
  by aesop

/-- Three registrations: the identities keep advancing, and the third does not reuse the
first or the second. -/
def w6ThreeLinks : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkInScope (ProgName.park 1) scopedChild 0)
      (ProgName.seqOf (ProgName.forkInScope (ProgName.park 2) scopedChild 0)
        (ProgName.forkInScope (ProgName.park 3) scopedChild 0)))
    [RunDecision.evaluate ⟨0⟩]

theorem w6_three_links_have_three_keys :
    scopeKeys w6ThreeLinks 0 = some [102, 103, 104] ∧
      exitOf w6ThreeLinks 1 = none ∧
      exitOf w6ThreeLinks 2 = none ∧
      exitOf w6ThreeLinks 3 = none :=
  by aesop

/-- A registration whose child finishes drops *its own* key, and the next registration takes
a new identity rather than the freed one: an old observer can never remove a later
registration. -/
def w6RemoveThenRegister : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkInScope (ProgName.value (Val.nat 3)) deferredChild 0)
      (ProgName.forkInScope (ProgName.park 2) scopedChild 0))
    [RunDecision.evaluate ⟨0⟩, RunDecision.fire ⟨0⟩]

theorem w6_freed_key_is_not_reused :
    scopeRows w6RemoveThenRegister = [[0, 0, 0, 102, 1], [0, 0, 0, 103, 2]] ∧
      scopeKeys w6RemoveThenRegister 0 = some [103] ∧
      exitOf w6RemoveThenRegister 1 = some (Exit.success (Val.nat 3)) ∧
      exitOf w6RemoveThenRegister 2 = none :=
  by aesop

/-- The same live fiber run into the same scope twice (`fiberRunIn`, `:5457-5460`), with the
caller left parked so both registrations are still live. -/
def w6RepeatedRunIn : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkOnly (ProgName.park 1) immediateChild)
      (ProgName.seqOf (ProgName.runInScope ⟨1⟩ 0)
        (ProgName.seqOf (ProgName.runInScope ⟨1⟩ 0) (ProgName.park 5))))
    [RunDecision.evaluate ⟨0⟩]

/-- One fiber registered twice holds two obligations, not one. -/
theorem w6_repeated_runIn_registers_twice :
    scopeRows w6RepeatedRunIn = [[0, 1, 0, 102, 1], [0, 1, 0, 103, 1]] ∧
      scopeKeys w6RepeatedRunIn 0 = some [102, 103] ∧
      exitOf w6RepeatedRunIn 1 = none :=
  by aesop

/-- The same two registrations, with the caller allowed to finish: its exit interrupts the
child, and the child's two observers drop exactly the two identities they were given. -/
def w6RepeatedRunInClosed : M :=
  replay scopeState
    (ProgName.seqOf (ProgName.forkOnly (ProgName.park 1) immediateChild)
      (ProgName.seqOf (ProgName.runInScope ⟨1⟩ 0) (ProgName.runInScope ⟨1⟩ 0)))
    [RunDecision.evaluate ⟨0⟩]

theorem w6_repeated_runIn_drops_both :
    scopeRows w6RepeatedRunInClosed = [[0, 1, 0, 102, 1], [0, 1, 0, 103, 1]] ∧
      scopeKeys w6RepeatedRunInClosed 0 = some [] ∧
      exitOf w6RepeatedRunInClosed 1 =
        some (interruptedWith ⟨0⟩ ⟨1⟩ (stores.stackAnnotations ⟨0⟩)) :=
  by aesop

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


-- Diagnostic only: the original five expected facts, evaluated before any repin.
#eval (fiberCount w6Parallel,
  decide (exitOf w6Parallel 1 = some (Exit.failure ⟨[Reason.fail (Err.tag 4) ReasonAnnotations.empty]⟩)),
  decide (exitOf w6Parallel 2 = some (Exit.success Val.unit)),
  decide (exitOf w6Parallel 0 = some (Exit.failure ⟨[Reason.fail (Err.tag 4) ReasonAnnotations.empty]⟩)),
  scopeClosed w6Parallel 4)
end Effect4.Machine.Witnesses
