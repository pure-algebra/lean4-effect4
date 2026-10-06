import Test.Program.SemaphoreScenarios
import Effect4.Program.Authoring.Mask

/-!
# Semaphore's acceptance traces, and the protected permit's red controls (rows 221, 222, 276)

Decisions row 221 names three acceptance traces of the waiting wrapper, and the wrapper's design
adds more (`docs/research/2026-10-05-claude-lead/waiting-design.md`, F5, F7 and proposal 5). The
Queue's battery runs them over the Queue (`Test/Program/QueueTraces.lean`). This battery runs
those that Semaphore has, over the library's operations
(`src/Effect4/Modules/Semaphore/Ops.lean`), and the controls of the protected permit. Each has
its positive control, and a fault that fails the promised property.

| # | The trace | The open part that it is a finite control of |
| --- | --- | --- |
| 1 | a notification before the await | `wait-registration-no-gap` |
| 2 | a cancellation between the release and the walk | `waiting-request-obligation-preserved` |
| 3 | a late delivery to an old hint after a second wait | `posted-task-decision-preserves` |
| 4 | a holder that is interrupted inside the take's mask | the protected permit, below |
| 5 | a waiter that is interrupted under a mask of the form's making | the protected permit, below |
| 6 | the signalling fiber exits before the dispatch | `posted-wake-profile-agrees` |
| 7 | the receiver's continuation that grows | `embedded-budget-sufficient` |
| 8 | the protected permit under a masked caller | the protected permit, below |

**The protected permit** is the card's proposed claim `semaphore-protected-permit` (concept
`scope-lifetime-finalization`, requirement R11;
`docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`, section 8). The registry does
not hold it yet. Traces 4 and 5 are the two red controls of `protectedBy`
(`src/Effect4/Modules/Waiting.lean`; decisions row 276, point 1): a take in its own mask loses
its permit under an interruption, and a wait inside a mask of the form's making cannot be
interrupted.

**A fault is a variant of Semaphore's part** (`Variant`): no withdrawal, one hint for every
round, or a helper with other fork options. The variant with no change is the library's
operation, tree for tree. Each faulty program builds: the checker types it. So each fault fails
the promised property, and not typing alone.

**A cancellation control records four observations apart** (decisions row 222): the commitment,
the operation's exit, the entry of the caller's continuation, and the fiber's exit. The
commitment is `taken` in the cell. A hook writes the operation's exit, and the step after the
operation writes a mark.

**The settings of every run.** The tape is the ordinary one, the root evaluated and then one
flush, with three more flushes. Traces 1 and 4 have tapes of their own. The fuel is 20000. A
child is forked with the default options: it starts at once.

Placement. Every guard is one run on one schedule, a finite control of the open part that its
trace names. None proves delivery, a cancellation law, a law of the mask, a bound or liveness,
and none is a host run. The programs under an operation budget are raw: the budget is a reserved
service, and the checker refuses its provision.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreTraces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.SemaphoreScenarios (Ops library mk verdict exitAt counts mark noNumbers count
  marks treeAt settle maskedCallerWith maskedCaller)
open Effect4.Modules
open Effect4.Semaphore (releaseStep withdrawStep)

/-! ## The rows of a run -/

abbrev Event := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- A row of a run's trace, as the controls read it: the fibers by number, and no payload. -/
inductive Row
  | forked (parent child : Nat) (detached : Bool)
  | started (fiber : Nat)
  | scheduled (owner : Nat)
  | ran (owner : Nat)
  | yielded (fiber : Nat)
  | parked (fiber : Nat)
  | resumed (fiber : Nat)
  | interrupted (target : Nat)
  | exited (fiber : Nat) (success : Bool)
  deriving DecidableEq, Repr

/-- The row of a machine event; `none` for an event that the controls do not read. -/
def rowOf : Event → Option Row
  | .forked parent child detached => some (.forked parent.value child.value detached)
  | .started fiber => some (.started fiber.value)
  | .scheduledTask owner _ _ => some (.scheduled owner.value)
  | .ranTask owner _ => some (.ran owner.value)
  | .yieldInjected fiber _ => some (.yielded fiber.value)
  | .parkedOn fiber _ => some (.parked fiber.value)
  | .resumedWith fiber _ _ => some (.resumed fiber.value)
  | .interruptRecorded _ target => some (.interrupted target.value)
  | .exited fiber (.success _) => some (.exited fiber.value true)
  | .exited fiber (.failure _) => some (.exited fiber.value false)
  | _ => none

/-- The fuel of each run here. -/
def fuel : Nat := 20000

/-- The ordinary tape, with three more flushes. -/
def plain : List Api.Decision := [Api.evaluate, Api.flush, Api.flush, Api.flush, Api.flush]

/-- A built source's run on a tape, through the checked session. -/
def runOn (tape : List Api.Decision) (src : Src NativeOp) : Option Run :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b =>
    (Run.open b "traces" { fuel := fuel, compileFuel := fuel }).play (Rows.tape tape)

/-- The root's exit of a built source's ordinary run, with the three more flushes. -/
def exitOf (src : Src NativeOp) : Option ExitV := (runOn plain src).bind (·.exit)

/-- The rows of a built source's ordinary run. -/
def rowsOf (src : Src NativeOp) : List Row :=
  ((runOn plain src).map fun r => r.machine.trace.filterMap rowOf).getD []

/-- Whether one row stands before another in a list of rows. -/
def before (first second : Row) (rows : List Row) : Bool :=
  match rows.idxOf? first, rows.idxOf? second with
  | some i, some j => decide (i < j)
  | _, _ => false

/-! ## The variants of Semaphore's part

A variant changes Semaphore's part of `take`, of `release` and of the protected form, and
nothing of the shared forms. The library's operation is the variant with no change. -/

/-- The knobs of a variant. Each default is the library's. -/
structure Variant where
  /-- Whether an interrupted wait withdraws its request. -/
  withdraws : Bool := true
  /-- The wrapper's loop at a restore site. -/
  retry : (Src NativeOp → Src NativeOp) → Ty → String → Waiter → Src NativeOp := waitRetryAt
  /-- The fork options of a release's helper. -/
  options : Effect4.Supervision.ForkOptions := posted

/-- Semaphore's part under a variant: the library's attempt, and the variant's withdrawal. -/
def takerOf (v : Variant) (q count : TermSrc) : Waiter :=
  { hint := .unit
    attempt := (Semaphore.taker q count).attempt
    withdraw := fun id =>
      if v.withdraws then Ref.modifyWith q (withdrawStep id) else succeed unit }

/-- The take's loop at a restore site, under a variant. -/
def takeAtOf (v : Variant) (restore : Src NativeOp → Src NativeOp) (q count : TermSrc) :
    Src NativeOp :=
  v.retry restore .nat Semaphore.ended (takerOf v q count)

/-- `release` under a variant: the library's, with the variant's fork options. -/
def releaseOf (v : Variant) (q count : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q (releaseStep count)) fun reply =>
      andThen
        (ifElse (tupleAt reply 1)
          (andThen (withFiber (Action.fork (Semaphore.walk q) v.options)) (succeed unit))
          (succeed unit))
        (succeed (tupleAt reply 0)))

/-- The operations of a variant. -/
def opsOf (v : Variant) : Ops :=
  { take := fun q count => uninterruptibleMaskWith fun restore => takeAtOf v restore q count
    release := releaseOf v
    withPermits := fun q count body =>
      protectedBy (fun restore => takeAtOf v restore q count) (fun _ => releaseOf v q count)
        (fun _ => body) }

-- The variant with no change is the library's operation, tree for tree.
#guard treeAt ["q", "n"] ((opsOf {}).take (var "q") (var "n")) ==
  treeAt ["q", "n"] (Semaphore.take (var "q") (var "n"))
#guard treeAt ["q", "n"] ((opsOf {}).release (var "q") (var "n")) ==
  treeAt ["q", "n"] (Semaphore.release (var "q") (var "n"))
#guard treeAt ["q", "n"] ((opsOf {}).withPermits (var "q") (var "n") (succeed (nat 1))) ==
  treeAt ["q", "n"] (Semaphore.withPermits (var "q") (var "n") (succeed (nat 1)))
#guard (treeAt ["q", "n"] ((opsOf {}).withPermits (var "q") (var "n") (succeed (nat 1)))).isSome

/-- **One hint for every round**: `waitRetryAt` with the hint allocated once, before the
loop. -/
def retryOneHintAt (restore : Src NativeOp → Src NativeOp) (result : Ty) (ended : String)
    (w : Waiter) : Src NativeOp :=
  bindWith (Deferred.make .unit .never) fun id =>
    bindWith (Deferred.make w.hint .never) fun hint =>
      bindWith
        (iterateWith noneT
          { cursorTy := some (.option result)
            while_ := fun cursor => notT (app "isSome" [cursor])
            body := fun _ =>
              w.attempt id hint
                (andThen (waitAt restore hint (w.withdraw id)) (succeed noneT))
                (fun answer => succeed (app "some" [answer]))
            step := fun _ answer => answer })
        fun last =>
          selectOptionWith last (failCause (Authoring.Cause.die (str ended))) fun answer =>
            succeed answer

/-! ## The pieces of a control -/

/-- **An operation under observation** (decisions row 222): the hook writes whether the
operation's exit is an interruption, and the step after the operation writes its answer as a
mark. So the operation's exit and the entry of the caller's continuation are two cells. -/
def observed (operation : Src NativeOp) (opExit entered : TermSrc) : Src NativeOp :=
  bindWith (onExitWith operation fun e => Ref.set opExit (app "causeIsInterrupt" [e]))
    fun answer => Ref.updateWith entered fun l => snoc l answer

/-- A body under an operation budget: the fiber yields before its operation `k` of an entry. -/
def budgeted (k : Nat) (body : Src NativeOp) : Src NativeOp :=
  provideService Env.maxOpsKey (nat k) body

/-- The raw run of a source on a tape. -/
def rawOn (tape : List Api.Decision) (src : Src NativeOp) : Option Api.Inspection :=
  (elaborateModule (mk src)).toOption.map fun p => Api.replay p fuel tape

/-- The taken count and the count of waiters, in the semaphore's cell: the first cell that a
run makes. -/
def cellOf (r : Api.Inspection) : Option (Nat × Nat) :=
  (r.machine.state.refs[0]?).bind fun cell =>
    match Machine.Record.read false cell "taken", Machine.Record.read false cell "waiters" with
    | some (.nat taken), some (.list waiters) => some (taken, waiters.length)
    | _, _ => none

/-! ## 1. A notification before the await

A waiter's hint resolves only in the helper's task. So a request that is notified before it
awaits loses nothing: its await answers at once, and its next attempt checks the count.

An operation budget stops the taker between its registration and its await. The root then
releases: its step finds the waiter enrolled, and it posts the helper. Two tapes follow. On the
first the taker's dispatcher fires before the root's: the taker awaits and parks, and the
helper's visit then resumes it. On the second the root's dispatcher fires first: the visit
selects the taker and resolves its hint, and the taker's await then answers at once. On both the
taker's next attempt follows the visit, and it takes.

These programs are raw: the budget is the reserved reference `Env.maxOpsKey`, and the checker
refuses its provision. `Api.replay` is the unchecked run. -/

/-- The root holds the one permit. A taker under an operation budget asks for it. The root
releases, and joins the taker. The answer: the free count that the release answers, and the
taker's answer. -/
def notified (k : Nat) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let _ ← Semaphore.take q (nat 1)
  let f ← fork (budgeted k (Semaphore.take q (nat 1)))
  let free ← Semaphore.release q (nat 1)
  let x ← join f
  return tuple [free, x]

/-- The cell and whether the root has exited, after each prefix of a tape but the empty one. -/
def stages (tape : List Api.Decision) (src : Src NativeOp) : List (Option (Nat × Nat) × Bool) :=
  (List.range tape.length).map fun n =>
    match rawOn (tape.take (n + 1)) src with
    | some r => (cellOf r, r.exit.isSome)
    | none => (none, false)

/-- The taker's dispatcher first: the await comes before the helper's task. -/
def awaitFirst : List Api.Decision := [Api.evaluate, .fire ⟨1⟩, .fire ⟨0⟩, Api.flush]

/-- The root's dispatcher first: the helper's task comes before the await. -/
def taskFirst : List Api.Decision := [Api.evaluate, .fire ⟨0⟩, .fire ⟨1⟩, Api.flush]

/-- A budget stops the taker between its registration and its await: after the root's
evaluation the taker has yielded once, it is enrolled, and the root's release left nothing
taken. -/
def stopsBetween (k : Nat) : Bool :=
  match rawOn [Api.evaluate] (notified k) with
  | some r =>
    (r.machine.trace.filterMap rowOf).count (.yielded 1) == 1 && cellOf r == some (0, 1)
  | none => false

-- The checker refuses the budget's provision, so the programs are raw.
#guard verdict (notified 23) = "typing: serviceUnknown"
-- The budgets that stop the taker between its registration and its await: 21 to 25. Below 21
-- the taker yields before its step, and from 26 it reaches its await with no yield.
#guard (List.range 32).filter stopsBetween = [21, 22, 23, 24, 25]

-- At each such budget, on both tapes: the root ends with the free count 1 and the taker's
-- count, and the permit is taken at the end.
#guard [21, 22, 23, 24, 25].all fun k =>
  [awaitFirst, taskFirst].all fun tape =>
    ((rawOn tape (notified k)).bind (·.exit)) == some (.success (.list [.nat 1, .nat 1])) &&
      (stages tape (notified k)).drop 3 == [(some (1, 0), true)]
-- The await before the task. After the taker's dispatcher the taker is still enrolled, and
-- nothing is taken: it parked at its hint. The root's dispatcher then runs the helper, whose
-- visit resumes the taker, and the taker's attempt runs inside that task.
#guard [21, 22, 23, 24, 25].all fun k =>
  (stages awaitFirst (notified k)).take 2 == [(some (0, 1), false), (some (0, 1), false)]
-- The task before the await. After the root's dispatcher the visit has selected the taker:
-- its entry left, and nothing is taken. A visit reserves nothing. The taker's dispatcher then
-- runs: its await answers at once, and its next attempt takes.
#guard [21, 22, 23, 24, 25].all fun k =>
  (stages taskFirst (notified k)).take 2 == [(some (0, 1), false), (some (0, 0), false)]

/-- The rows of a raw run on a tape. -/
def rawRows (tape : List Api.Decision) (src : Src NativeOp) : List Row :=
  ((rawOn tape src).map fun r => r.machine.trace.filterMap rowOf).getD []

-- The await before the task, at the budget 25. The taker's dispatcher runs: the taker parks at
-- its hint. Then the root's dispatcher runs the helper, fiber 2, which resumes the taker.
#guard rawRows awaitFirst (notified 25) =
  [.started 0, .forked 0 1 false, .started 1, .yielded 1, .parked 1, .forked 0 2 true,
   .scheduled 0, .parked 0, .ran 1, .resumed 1, .started 1, .parked 1, .ran 0, .started 2,
   .resumed 1, .started 1, .exited 1 true, .resumed 0, .started 0, .exited 0 true,
   .exited 2 true]
-- The task before the await. The helper runs and exits, and it resumes nobody. The taker's
-- dispatcher then runs: the taker's await answers at once, so no park follows its resume.
#guard rawRows taskFirst (notified 25) =
  [.started 0, .forked 0 1 false, .started 1, .yielded 1, .parked 1, .forked 0 2 true,
   .scheduled 0, .parked 0, .ran 0, .started 2, .exited 2 true, .ran 1, .resumed 1, .started 1,
   .exited 1 true, .resumed 0, .started 0, .exited 0 true]
-- Red control of the two tapes: they are two schedules.
#guard rawRows awaitFirst (notified 25) != rawRows taskFirst (notified 25)

/-! ## 2. A cancellation between the release and the walk

The root holds the one permit. Two takers wait, A and then B. The root releases: its step finds
a waiter, and it posts the helper. The root interrupts A before the helper's task runs. -/

/-- The scenario, with A under either caller. The answer: the free count that the release
answers; the counts after A's exit and before the helper's task; the counts after that task;
whether A's operation ended by an interruption; the count of A's continuation's marks; and
whether A's fiber and B's fiber ended by an interruption. The root interrupts B at the end: a B
that took has exited by then. -/
def cancelled (ops : Ops) (maskedCaller : Bool) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let opExit ← Ref.make (bool false)
  let entered ← Ref.make noNumbers
  let _ ← Semaphore.take q (nat 1)
  let fa ← fork ((if maskedCaller then uninterruptible else id)
    (observed (ops.take q (nat 1)) opExit entered))
  let fb ← fork (ops.take q (nat 1))
  let free ← ops.release q (nat 1)
  let _ ← withFiber (Action.interrupt fa)
  let ea ← await fa
  let left ← counts q
  let _ ← yieldNow 0
  let _ ← yieldNow 0
  let after ← counts q
  let _ ← withFiber (Action.interrupt fb)
  let eb ← await fb
  let oe ← Ref.get opExit
  let en ← Ref.get entered
  return tuple [free, left, after, oe, len en, app "causeIsInterrupt" [ea],
    app "causeIsInterrupt" [eb]]

#guard verdict (cancelled library false) = "built" && verdict (cancelled library true) = "built"
-- **An interruptible caller**: the wait is interrupted, and the withdrawal wins. Nothing is
-- committed to A: its entry leaves, nothing is taken, its operation's exit is an interruption,
-- its continuation is not entered, and its fiber's exit is an interruption. The helper's visit
-- then finds B: B takes, so one permit is taken, nobody waits, and B's fiber ended with a take.
#guard exitOf (cancelled library false) = some (.success (.list
  [.nat 1, count 0 [1] [1], count 1 [] [], .bool true, .nat 0, .bool true, .bool false]))
-- **A masked caller**, beside it: the restore is the identity, so A stays enrolled. The
-- commitment is A's: the visit selects A, and A takes. Its operation's exit is no
-- interruption, and its continuation is entered once. Its fiber's exit is an interruption,
-- when its caller's mask ends. The permit stays taken: a raw take records no holder. B is
-- never served: it waits until the root interrupts it.
#guard exitOf (cancelled library true) = some (.success (.list
  [.nat 1, count 1 [1] [1], count 1 [1] [1], .bool false, .nat 1, .bool true, .bool true]))
-- The four observations are four values: under the masked caller the operation's exit and the
-- fiber's exit differ, and under the interruptible caller they agree.

-- The helper is fiber 3, forked by the root. Under the interruptible caller A, fiber 1, exits
-- before the root's dispatcher runs the helper, and the helper's visit resumes B, fiber 2.
#guard before (.exited 1 false) (.started 3) (rowsOf (cancelled library false)) &&
  before (.started 3) (.resumed 2) (rowsOf (cancelled library false)) &&
  before (.exited 2 true) (.exited 3 true) (rowsOf (cancelled library false))

-- **Fault: no withdrawal.** A's entry stays after its fiber is gone: two waiters stand where
-- one request waits. The live scan then spends one visit on the entry of nobody.
#guard verdict (cancelled (opsOf { withdraws := false }) false) = "built"
#guard exitOf (cancelled (opsOf { withdraws := false }) false) = some (.success (.list
  [.nat 1, count 0 [1, 1] [0, 1], count 1 [] [], .bool true, .nat 0, .bool true, .bool false]))

/-! ## 3. A late delivery to an old hint after the request waits again

No step of the first profile wakes a waiter whose count does not fit. So this control posts the
wakes itself: two helpers for the waiter's hint, while the permit is held. The first resumes the
waiter: it tries again, does not take, and enrols again with a fresh hint and a new stamp. The
second is the late delivery: it resolves the old hint, which nobody awaits. -/

/-- The scenario. The answer: the count of waiters after both helpers, whether the waiter's
hint is still the first one, its stamp, and its answer after the root's release. -/
def rearmed (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let _ ← Semaphore.take q (nat 1)
  let f ← fork (ops.take q (nat 1))
  let first ← Ref.get q
  selectOptionWith (app "get" [field first "waiters", nat 0])
    (succeed (tuple [nat 99, bool true, nat 99, nat 99])) fun enrolled => eff do
      let _ ← postAll (field first "waiters") unit
      let _ ← postAll (field first "waiters") unit
      let _ ← yieldNow 0
      let second ← Ref.get q
      selectOptionWith (app "get" [field second "waiters", nat 0])
        (succeed (tuple [nat 98, bool true, nat 98, nat 98])) fun again => eff do
          let _ ← Semaphore.release q (nat 1)
          let x ← join f
          return tuple [len (field second "waiters"),
            same (field enrolled "hint") (field again "hint"), field again "stamp", x]

#guard verdict (rearmed library) = "built"
-- After both helpers the waiter is enrolled once, with another hint than its first, at the
-- stamp 1. The release's walk then reaches the fresh hint, and the waiter takes.
#guard exitOf (rearmed library) =
  some (.success (.list [.nat 1, .bool false, .nat 1, .nat 1]))
-- The first helper is fiber 2: it resumes the waiter, fiber 1, which parks again. The second
-- helper is fiber 3: it starts and exits, and it resumes nobody.
#guard (rowsOf (rearmed library)).take 18 =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 true, .scheduled 0,
   .forked 0 3 true, .scheduled 0, .parked 0, .ran 0, .started 2, .resumed 1, .started 1,
   .parked 1, .exited 2 true, .ran 0, .started 3, .exited 3 true]
-- The waiter never yields by its operation budget: each wait is a park.
#guard (rowsOf (rearmed library)).count (.yielded 1) = 0
-- The ordinary run ends at the truth lane's fuel.
#guard (exitAt 1000 (rearmed library)).isSome

-- **Fault: one hint for every round.** After the first wake the hint is resolved for good, so
-- each later wait answers at once: the waiter tries again and again without a park, and each
-- round enrols it again. It keeps its first hint, and its stamp is 157 when its operation
-- budget stops it. The ordinary run has no exit at the truth lane's fuel.
#guard verdict (rearmed (opsOf { retry := retryOneHintAt })) = "built"
#guard exitOf (rearmed (opsOf { retry := retryOneHintAt })) =
  some (.success (.list [.nat 1, .bool true, .nat 157, .nat 1]))
#guard (rowsOf (rearmed (opsOf { retry := retryOneHintAt }))).count (.yielded 1) != 0
#guard (exitAt 1000 (rearmed (opsOf { retry := retryOneHintAt }))).isNone

/-! ## 4. A holder that is interrupted inside the take's mask

The first red control of `protectedBy` (decisions row 276, point 1). A fiber that is
interrupted while it is masked takes the interruption where its mask ends. In the protected form
the hook is installed before that point. A take that holds its own mask ends that mask before
the hook: the interruption lands between them, no release runs, and the permit is lost.

A yield can stand inside a masked region: a yield is no interruption. The first two forms write
one such yield out, after the take's commit. The last two write none: the library's own forms
run under an operation budget, and the machine's yield at the budget stands there. -/

/-- The take's loop, and then one yield inside the mask. -/
def takeThenYield (q count : TermSrc) (restore : Src NativeOp → Src NativeOp) : Src NativeOp :=
  bindWith (waitRetryAt restore .nat Semaphore.ended (Semaphore.taker q count)) fun got =>
    andThen (yieldNow 0) (succeed got)

/-- One region: the protected form, with the yield inside it. -/
def oneRegion (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  protectedBy (takeThenYield q count) (fun _ => Semaphore.release q count) (fun _ => body)

/-- Two regions: the take in its own mask, and then the hook. -/
def twoRegions (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  bindWith (uninterruptibleMaskWith fun restore => takeThenYield q count restore) fun _ =>
    onExitWith body fun _ => Semaphore.release q count

/-- A total of 1. A takes it and yields inside its mask. A second child requests A's
interruption while A is masked. The answer: the counts while A holds, the counts after the
root's four yields, and whether A's exit is an interruption. -/
def interruptedHolder (use : TermSrc → TermSrc → Src NativeOp → Src NativeOp) : Src NativeOp :=
  eff do
    let q ← Semaphore.make 1
    let a ← fork (use q (nat 1) (succeed unit))
    let held ← counts q
    let _ ← fork (withFiber (Action.interrupt a))
    let _ ← settle
    let after ← counts q
    let e ← await a
    return tuple [held, after, app "causeIsInterrupt" [e]]

#guard [interruptedHolder oneRegion, interruptedHolder twoRegions].map verdict =
  ["built", "built"]
-- One region. The interruption waits for the restore site. The hook is installed by then, so
-- the release runs: nothing is taken at the end.
#guard exitOf (interruptedHolder oneRegion) = some (.success (.list
  [count 1 [] [], count 0 [] [], .bool true]))
-- Two regions. The interruption lands at the first mask's end, before the hook is installed.
-- No release runs: one permit stays taken by a fiber that has exited.
#guard exitOf (interruptedHolder twoRegions) = some (.success (.list
  [count 1 [] [], count 1 [] [], .bool true]))
#guard exitOf (interruptedHolder twoRegions) != exitOf (interruptedHolder oneRegion)

/-- The library's take, and then the hook: two regions, with no yield written. -/
def takeThenHook (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  bindWith (Semaphore.take q count) fun _ =>
    onExitWith body fun _ => Semaphore.release q count

/-- The scenario under an operation budget for A alone. The answer: the counts while the root
first reads them, and the counts after its four yields. -/
def holderUnder (k : Nat) (use : TermSrc → TermSrc → Src NativeOp → Src NativeOp) :
    Src NativeOp := eff do
  let q ← Semaphore.make 1
  let a ← fork (budgeted k (use q (nat 1) (succeed unit)))
  let held ← counts q
  let _ ← fork (withFiber (Action.interrupt a))
  let _ ← settle
  let after ← counts q
  return tuple [held, after]

/-- The taken counts of the two readings, on the ordinary tape with three more flushes. -/
def takenUnder (k : Nat) (use : TermSrc → TermSrc → Src NativeOp → Src NativeOp) :
    Option (Val × Val) :=
  match (rawOn plain (holderUnder k use)).bind (·.exit) with
  | some (.success (.list [.list (held :: _), .list (after :: _)])) => some (held, after)
  | _ => none

-- The library's `withPermits` under the budgets 13 and 27: A yields inside the mask, before
-- its take's step at 13 and after it at 27. The interruption waits, and the release runs:
-- nothing is taken at the end.
#guard takenUnder 13 Semaphore.withPermits = some (.nat 0, .nat 0) &&
  takenUnder 27 Semaphore.withPermits = some (.nat 1, .nat 0)
-- The library's `take` and then the hook, at the same two budgets: the permit is lost.
#guard takenUnder 13 takeThenHook = some (.nat 0, .nat 1) &&
  takenUnder 27 takeThenHook = some (.nat 1, .nat 1)
-- Measured at each budget from 8 to 35: the two-region form loses the permit at the fifteen
-- budgets from 13 to 27, and at no other. At 12 A yields before the mask, where it is
-- interruptible: nothing is taken. At 28 the two-region form has installed its hook when A
-- yields, so its release runs.
#guard (List.range' 8 28).filter
    (fun k => (takenUnder k takeThenHook).map (·.2) == some (.nat 1)) = List.range' 13 15
-- The library's form loses it at none of them.
#guard (List.range' 8 28).all fun k =>
  (takenUnder k Semaphore.withPermits).map (·.2) == some (.nat 0)

/-! ## 5. A waiter that is interrupted under a mask of the form's making

The second red control of `protectedBy`. The library's `take` holds its own mask. Inside a mask
that a form opens around it, its restore gives that mask's state: the wait is masked, whatever
the caller. So an interruption does not reach the wait, the withdrawal never runs, and the
request commits a take after its own interruption. The protected form hands the take's loop the
one mask's restore, which is the caller's state.

Each form's hook writes a mark, so the log shows whether a take was committed. -/

/-- The protected form, with a hook that writes a mark before the release. -/
def marked (log q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  protectedBy (fun restore => waitRetryAt restore .nat Semaphore.ended (Semaphore.taker q count))
    (fun _ => andThen (mark log (nat 9)) (Semaphore.release q count)) (fun _ => body)

/-- The library's take, with its own mask, inside a mask of the form's making. -/
def nested (log q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (Semaphore.take q count) fun _ =>
      onExitWith (restore body) fun _ => andThen (mark log (nat 9)) (Semaphore.release q count)

/-- A total of 1, held by the root. A waits in a form, and a second child requests A's
interruption. The root then releases. The answer: the counts while A waits; the counts after
the interrupt's request; the free count that the release answers; the counts at the end; and
the hook's marks. -/
def interruptedWaiter (use : TermSrc → TermSrc → TermSrc → Src NativeOp → Src NativeOp) :
    Src NativeOp := eff do
  let q ← Semaphore.make 1
  let log ← Ref.make noNumbers
  let _ ← Semaphore.take q (nat 1)
  let a ← fork (use log q (nat 1) (succeed unit))
  let waiting ← counts q
  let _ ← fork (withFiber (Action.interrupt a))
  let _ ← settle
  let left ← counts q
  let answer ← Semaphore.release q (nat 1)
  let _ ← settle
  let after ← counts q
  let l ← Ref.get log
  return tuple [waiting, left, answer, after, l]

#guard [interruptedWaiter marked, interruptedWaiter nested].map verdict = ["built", "built"]
-- The protected form. The wait is interrupted: A's entry leaves, and A commits nothing. No
-- hook runs. The release then answers 1 free, and nothing is taken at the end.
#guard exitOf (interruptedWaiter marked) = some (.success (.list
  [count 1 [1] [0], count 1 [] [], .nat 1, count 0 [] [], marks []]))
-- The nested mask. The wait cannot be interrupted: A's entry stays. After the root's release
-- the walk resumes A, and A takes after its own interruption: the hook's mark is written.
#guard exitOf (interruptedWaiter nested) = some (.success (.list
  [count 1 [1] [0], count 1 [1] [0], .nat 1, count 0 [] [], marks [9]]))
#guard exitOf (interruptedWaiter nested) != exitOf (interruptedWaiter marked)
-- The protected form with the marking hook is the library's form but for the mark: a body that
-- runs to its end writes the mark once.
#guard exitOf (eff do
    let q ← Semaphore.make 1
    let log ← Ref.make noNumbers
    let _ ← marked log q (nat 1) (succeed unit)
    let after ← counts q
    let l ← Ref.get log
    return tuple [after, l]) = some (.success (.list [count 0 [] [], marks [9]]))

/-! ## 6. The signalling fiber exits before the dispatch

A taker waits. A second fiber releases and exits at once. Its helper is a daemon, and its start
is already posted on the releasing fiber's dispatcher. A protected body's hook is such a
release: the case P1 of `Test/Program/SemaphoreScenarios.lean` runs it, where A exits before
its helper runs. -/

/-- The scenario. The answer: whether the releasing fiber's exit is an interruption, and the
taker's answer. -/
def signallerExits (ops : Ops) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let _ ← Semaphore.take q (nat 1)
  let ft ← fork (ops.take q (nat 1))
  let fs ← fork (ops.release q (nat 1))
  let es ← await fs
  let x ← join ft
  return tuple [app "causeIsInterrupt" [es], x]

#guard verdict (signallerExits library) = "built"
-- The releasing fiber, fiber 2, exits with its answer. Its dispatcher then runs the helper,
-- fiber 3, whose visit resumes the taker.
#guard exitOf (signallerExits library) = some (.success (.list [.bool false, .nat 1]))
#guard before (.exited 2 true) (.ran 2) (rowsOf (signallerExits library))
#guard (rowsOf (signallerExits library)).contains (.forked 2 3 true)

-- **Fault: the helper as a supervised, interruptible child.** The releasing fiber's exit
-- interrupts its children. The helper is interrupted before its first visit: the wake is
-- lost, the taker waits for good beside a free permit, and the root has no exit.
#guard verdict (signallerExits (opsOf { options := ⟨false, false, .interruptible⟩ })) = "built"
#guard (exitOf (signallerExits (opsOf { options := ⟨false, false, .interruptible⟩ }))).isNone
#guard (rowsOf (signallerExits (opsOf { options := ⟨false, false, .interruptible⟩ }))).contains
  (.exited 3 false)

/-! ## 7. The receiver's continuation that grows

The helper's task runs the resumed waiter: its next attempt, and then its caller's continuation,
under the task's own budget (decisions rows 226, 238 and 259). One visit reaches the resumed
caller's work up to its own cut. Here the taker's continuation is a loop of `n` steps. The
measure is the least fuel at which the flush of the helper's task ends the root.

**No bound is claimed.** The numbers are measured on this program at these lengths. -/

/-- A taker whose continuation runs `n` steps; the root releases, and joins it. -/
def grows (n : Nat) : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let steps ← Ref.make (nat 0)
  let _ ← Semaphore.take q (nat 1)
  let f ← fork (eff do
    let x ← Semaphore.take q (nat 1)
    let _ ← forRange (nat 0) (nat n) fun _ => Ref.updateWith steps fun c => app "succ" [c]
    return x)
  let _ ← Semaphore.release q (nat 1)
  let x ← join f
  let c ← Ref.get steps
  return tuple [x, c]

/-- The root's exit after one flush at a fuel, and then after five more flushes at the ample
fuel. The root is evaluated at the ample fuel first: it parks at its join, with the helper's
start posted. -/
def afterFlush (src : Src NativeOp) (budget : Nat) : Option (Bool × Bool) :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b =>
    let ample : Api.Budget := { fuel := fuel, compileFuel := fuel }
    let evaluated := (Run.open b "traces" ample).control Api.evaluate
    let one := ({ evaluated with budget := { fuel := budget, compileFuel := fuel } } : Run).control
      Api.flush
    let more := (List.range 5).foldl (fun (s : Run) _ => s.control Api.flush)
      ({ one with budget := ample } : Run)
    (one.exit.isSome, more.exit.isSome)

/-- The lengths, each with the least fuel of the delivery's flush that was measured for it. -/
def measured : List (Nat × Nat) :=
  [(0, 49), (1, 52), (2, 55), (4, 61), (8, 73), (16, 97), (32, 145), (64, 241)]

-- Each program builds, and it answers its count and its count of steps.
#guard measured.all fun (n, _) =>
  exitOf (grows n) == some (.success (.list [.nat 1, .nat n]))
-- At the measured fuel the flush ends the root. The empty continuation is the control: 49.
#guard measured.all fun (n, least) => afterFlush (grows n) least == some (true, true)
-- At one less it does not. And five more flushes at the ample fuel do not end it either: the
-- cut inside the dispatch lost the work that remained, and a later flush is no resumption.
-- Decisions row 226 excludes that cut from the first profile, so this is the excluded case,
-- and no fault of the walk.
#guard measured.all fun (n, least) => afterFlush (grows n) (least - 1) == some (false, false)
-- The measured fuel grows with the continuation: three for each step, at these lengths.
#guard measured.all fun (n, least) => least == 49 + 3 * n

/-! ## 8. The protected permit under a masked caller

The scenario is `maskedCallerWith` of `Test/Program/SemaphoreScenarios.lean`. Under a masked
caller the mask's restore is the identity: the wait is not interrupted, the request stays
enrolled, and it takes. The body runs inside the caller's mask, the release runs at its exit,
and the fiber is interrupted when its caller's mask ends.

The red control is the earlier fixture's form (`Written.ops`): it restores with `interruptible`,
whatever its caller, so its wait is interrupted under the masked caller. -/

#guard verdict maskedCaller = "built"
-- With the mask that restores: the waiter stays enrolled after the interrupt's request. The
-- body runs with the permit taken, and it writes 11. The child's exit is an interruption, and
-- the release ran: nothing is taken at the end, and nobody waits.
#guard exitOf maskedCaller = some (.success (.list
  [count 1 [1] [0], .nat 11, .bool true, count 0 [] []]))
-- The ordinary run gives the same answer at the truth lane's fuel.
#guard exitAt 1000 maskedCaller = exitOf maskedCaller
-- Red control: the stand-in restores with `interruptible`. Its wait is interrupted under the
-- masked caller: the waiter withdraws, and its body never runs.
#guard exitOf (maskedCallerWith Test.Program.SemaphoreScenarios.Written.ops) =
  some (.success (.list [count 1 [] [], .nat 0, .bool true, count 0 [] []]))
-- The child is fiber 1 and its interruptor fiber 2. The helper is fiber 3: it resumes the
-- child, which exits by the interruption only then, and the interruptor after it.
#guard rowsOf maskedCaller =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 false, .started 2,
   .interrupted 1, .parked 2, .forked 0 3 true, .scheduled 0, .parked 0, .ran 0, .started 3,
   .resumed 1, .started 1, .exited 1 false, .resumed 2, .started 2, .exited 2 true, .resumed 0,
   .started 0, .exited 0 true, .exited 3 true]

end Test.Program.SemaphoreTraces
