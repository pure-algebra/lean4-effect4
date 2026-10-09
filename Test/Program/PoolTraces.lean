import Test.Program.PoolPublic
import Test.Program.SemaphoreTraces
import Effect4.Program.Authoring.Mask

/-!
# Pool's acceptance traces, and the red controls of the lease and of the close (rows 221, 222, 268, 276, 279)

Decisions row 221 names three acceptance traces of the waiting wrapper, and the wrapper's design
adds more (`docs/research/2026-10-05-claude-lead/waiting-design.md`, F5, F7 and proposal 5). The
Queue's battery and Semaphore's run them over their modules (`Test/Program/QueueTraces.lean`,
`Test/Program/SemaphoreTraces.lean`). This battery runs them over Pool's `use`
(`src/Effect4/Library/Pool/Ops.lean`), with the controls of the protected lease and of the
close. Each has its positive control, and a fault that fails the promised property.

| # | The trace | The open part that it is a finite control of |
| --- | --- | --- |
| 1 | a notification before the await | `wait-registration-no-gap` |
| 2 | a cancellation between the return and the wake | `waiting-request-obligation-preserved` |
| 3 | a late delivery to an old hint after a second wait | `posted-task-decision-preserves` |
| 4 | a holder that is interrupted inside the lease's mask | the protected lease, below |
| 5 | a waiter that is interrupted under a mask of the form's making | the protected lease, below |
| 6 | the returning fiber exits before the dispatch | `posted-wake-profile-agrees` |
| 7 | the receiver's continuation that grows | `embedded-budget-sufficient` |
| 8 | the protected lease under a masked caller | the protected lease, below |
| 9 | a borrow at a closing pool, and under a masked caller | `pool-close-waits`, and decisions row 279 |

**The protected lease** is the card's proposed claim `pool-lease-return` (concept
`scope-lifetime-finalization`, requirement R11;
`docs/research/2026-10-05-claude-lead/module-cards/pool.md`, section 8). Traces 4 and 5 are the
two red controls of `protectedBy` at Pool (decisions row 276, point 1): a lease in its own mask
is lost under an interruption, and a wait inside a mask of the form's making cannot be
interrupted. The red control of the close is in `Test/Program/PoolPublic.lean`: a close that
does not wait finalizes an item that a borrower still holds.

**A fault is a variant of Pool's part** (`Variant`): no withdrawal, one hint for every round, or
a helper with other fork options. The variant with no change is the library's operation, tree
for tree. Each faulty program builds: the checker types it. So each fault fails the promised
property, and not typing alone.

**The pool of a trace is its cell alone**, but in trace 9. A trace makes the cell by
`Ref.make`, so no scope's close stands behind it. A fault that loses a lease then leaves a run
that ends, and the lost lease is read in the cell.

**The settings of every run.** The tape is the ordinary one, the root evaluated and then one
flush, with three more flushes. Traces 1 and 4 have tapes or budgets of their own. The fuel is
20000. A child is forked with the default options: it starts at once.

Placement. Every guard is one run on one schedule, a finite control of the open part that its
trace names. None proves delivery, a cancellation law, a law of the mask, a bound or liveness,
and none is a host run. The programs under an operation budget are raw: the budget is a reserved
service, and the checker refuses its provision.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolTraces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Test.Program.PoolScenarios (mk verdict noRows say settle snap rows)
open Test.Program.PoolPublic (treeAt snapshot exitAt acquire holding library)
open Test.Program.SemaphoreTraces (Row rowOf before budgeted fuel plain runOn exitOf rowsOf rawOn
  rawRows)

/-! ## The variants of Pool's part

A variant changes Pool's part of the lease and of the return, and nothing of the shared forms.
The library's `use` is the variant with no change. -/

/-- The knobs of a variant. Each default is the library's. -/
structure Variant where
  /-- Whether an interrupted wait withdraws its request. -/
  withdraws : Bool := true
  /-- The wrapper's loop at a restore site. -/
  retry : (Src NativeOp → Src NativeOp) → Ty → String → Waiter → Src NativeOp := waitRetryAt
  /-- The fork options of a return's helper. -/
  options : Effect4.Supervision.ForkOptions := posted

/-- Pool's part under a variant: the library's attempt, and the variant's withdrawal. -/
def borrowerOf (v : Variant) (pool : TermSrc) : Waiter :=
  { hint := .unit
    attempt := (Pool.borrower pool).attempt
    withdraw := fun id =>
      if v.withdraws then Ref.modifyWith pool (Pool.withdrawStep id) else succeed unit }

/-- The lease at a restore site, under a variant. -/
def leaseOf (v : Variant) (A : Ty) (pool : TermSrc) (restore : Src NativeOp → Src NativeOp) :
    Src NativeOp :=
  bindWith (v.retry restore (.option (Pool.itemTy A)) Pool.ended (borrowerOf v pool)) fun got =>
    selectOptionWith got Pool.refused fun item => succeed item

/-- The return under a variant: the library's, with the variant's fork options. -/
def giveBackOf (v : Variant) (pool item : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith pool (Pool.returnStep (field item "stamp") (field item "lease")))
    fun reply =>
      ifElse (tupleAt reply 1)
        (andThen (withFiber (Action.fork (Pool.wake pool (nat 1)) v.options)) (succeed unit))
        (succeed unit)

/-- `use` under a variant. -/
def useOf (v : Variant) (A : Ty) (pool : TermSrc) (body : TermSrc → Src NativeOp) :
    Src NativeOp :=
  protectedBy (leaseOf v A pool) (giveBackOf v pool) (fun item => body (field item "resource"))

/-- The form of `use` that a scenario takes. -/
abbrev Use := Ty → TermSrc → (TermSrc → Src NativeOp) → Src NativeOp

-- The variant with no change is the library's operation, tree for tree.
#guard (treeAt ["p"] (useOf {} .nat (var "p") fun r => succeed r)).isSome &&
  treeAt ["p"] (useOf {} .nat (var "p") fun r => succeed r) ==
    treeAt ["p"] (Pool.use .nat (var "p") fun r => succeed r)
-- Red control of the comparison: a changed variant is another tree.
#guard treeAt ["p"] (useOf { withdraws := false } .nat (var "p") fun r => succeed r) !=
  treeAt ["p"] (Pool.use .nat (var "p") fun r => succeed r)

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

/-- A pool of one item, at the resource 1: the cell alone, with no scope's close. -/
def cellOnly : Src NativeOp := Ref.make (Pool.initial .nat [nat 1])

/-- The idle stamps' count, the borrowed items' count and the waiters' count, in the pool's
cell: the first cell that a run makes. -/
def cellOf (r : Api.Inspection) : Option (Nat × Nat × Nat) :=
  (r.machine.state.refs[0]?).bind fun cell =>
    match Machine.Record.read false cell "available", Machine.Record.read false cell "items",
      Machine.Record.read false cell "waiters" with
    | some (.list idle), some (.list items), some (.list waiters) =>
      some (idle.length, items.length - idle.length, waiters.length)
    | _, _, _ => none

/-! ## 1. A notification before the await

A waiter's hint resolves only in the helper's task. So a request that is notified before it
awaits loses nothing: its await answers at once, and its next attempt checks the cell.

An operation budget stops the borrower between its enrolment and its await. The holder then
returns: its step finds the waiter enrolled, and it posts the helper. Two tapes follow. On the
first the borrower's dispatcher fires before the holder's: the borrower awaits and parks, and
the helper then resumes it. On the second the holder's dispatcher fires first: the selection
takes the borrower and resolves its hint, and the borrower's await then answers at once. On
both the borrower's next attempt follows the selection, and it leases.

These programs are raw: the budget is the reserved reference `Env.maxOpsKey`, and the checker
refuses its provision. `Api.replay` is the unchecked run. -/

/-- H holds the item. A borrower under an operation budget asks for it. The root opens H's
gate, and joins the borrower. The answer: the resource that the borrower's body reads. H is
fiber 1 and the borrower fiber 2. -/
def notified (k : Nat) : Src NativeOp := eff do
  let pool ← cellOnly
  let gH ← Deferred.make .unit .never
  let _ ← fork (Pool.use .nat pool fun _ => Deferred.await gH)
  let f ← fork (budgeted k (Pool.use .nat pool fun r => succeed r))
  let _ ← Deferred.succeed gH unit
  join f

/-- The cell and whether the root has exited, after each prefix of a tape but the empty one. -/
def stages (tape : List Api.Decision) (src : Src NativeOp) :
    List (Option (Nat × Nat × Nat) × Bool) :=
  (List.range tape.length).map fun n =>
    match rawOn (tape.take (n + 1)) src with
    | some r => (cellOf r, r.exit.isSome)
    | none => (none, false)

/-- The borrower's dispatcher first: the await comes before the helper's task. -/
def awaitFirst : List Api.Decision := [Api.evaluate, .fire ⟨2⟩, .fire ⟨1⟩, Api.flush]

/-- The holder's dispatcher first: the helper's task comes before the await. -/
def taskFirst : List Api.Decision := [Api.evaluate, .fire ⟨1⟩, .fire ⟨2⟩, Api.flush]

/-- A budget stops the borrower between its enrolment and its await: after the root's
evaluation the borrower has yielded once, it is enrolled, and the holder's return left the item
idle. -/
def stopsBetween (k : Nat) : Bool :=
  match rawOn [Api.evaluate] (notified k) with
  | some r =>
    (r.machine.trace.filterMap rowOf).count (.yielded 2) == 1 && cellOf r == some (1, 0, 1)
  | none => false

-- The checker refuses the budget's provision, so the programs are raw.
#guard verdict (notified 25) = "typing: serviceUnknown"
-- The budgets that stop the borrower between its enrolment and its await: 23 to 27. Below 23
-- the borrower yields before its step, and from 28 it reaches its await with no yield.
#guard (List.range 40).filter stopsBetween = [23, 24, 25, 26, 27]

-- At each such budget, on both tapes: the root ends with the resource 1, the item is idle
-- again at the end, and nobody waits.
#guard [23, 24, 25, 26, 27].all fun k =>
  [awaitFirst, taskFirst].all fun tape =>
    ((rawOn tape (notified k)).bind (·.exit)) == some (.success (.nat 1)) &&
      (stages tape (notified k)).drop 3 == [(some (1, 0, 0), true)]
-- The await before the task. After the borrower's dispatcher the borrower is still enrolled,
-- and the item is idle: it parked at its hint. The holder's dispatcher then runs the helper,
-- which resumes the borrower, and the borrower's attempt runs inside that task.
#guard [23, 24, 25, 26, 27].all fun k =>
  (stages awaitFirst (notified k)).take 2 == [(some (1, 0, 1), false), (some (1, 0, 1), false)]
-- The task before the await. After the holder's dispatcher the selection has taken the
-- borrower: its entry left, and the item is still idle. A selection reserves nothing. The
-- borrower's dispatcher then runs: its await answers at once, and its next attempt leases.
#guard [23, 24, 25, 26, 27].all fun k =>
  (stages taskFirst (notified k)).take 2 == [(some (1, 0, 1), false), (some (1, 0, 0), false)]

-- The await before the task, at the budget 27. The borrower's dispatcher runs: the borrower
-- parks at its hint. Then the holder's dispatcher runs the helper, fiber 3, which resumes the
-- borrower. The borrower yields once more at its budget, inside its lease.
#guard rawRows awaitFirst (notified 27) =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 false, .started 2,
   .yielded 2, .parked 2, .resumed 1, .started 1, .forked 1 3 true, .scheduled 1, .exited 1 true,
   .parked 0, .ran 2, .resumed 2, .started 2, .parked 2, .ran 1, .started 3, .resumed 2,
   .started 2, .yielded 2, .parked 2, .exited 3 true, .ran 2, .resumed 2, .started 2,
   .exited 2 true, .resumed 0, .started 0, .exited 0 true]
-- The task before the await. The helper runs and exits, and it resumes nobody. The borrower's
-- dispatcher then runs: the borrower's await answers at once, so no park follows its resume
-- but the park of its budget's yield.
#guard rawRows taskFirst (notified 27) =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 false, .started 2,
   .yielded 2, .parked 2, .resumed 1, .started 1, .forked 1 3 true, .scheduled 1, .exited 1 true,
   .parked 0, .ran 1, .started 3, .exited 3 true, .ran 2, .resumed 2, .started 2, .yielded 2,
   .parked 2, .ran 2, .resumed 2, .started 2, .exited 2 true, .resumed 0, .started 0,
   .exited 0 true]
-- Red control of the two tapes: they are two schedules.
#guard rawRows awaitFirst (notified 27) != rawRows taskFirst (notified 27)

/-! ## 2. A cancellation between the return and the wake

H holds the item. Two borrowers wait, A and then B. H returns: its step finds a waiter, and it
posts the helper. The root interrupts A before the helper's task runs. -/

/-- The scenario, with A under either caller. A's body writes the row `[1, 1, resource]`, and a
hook around A's `use` writes whether its exit is an interruption. The answer: the cell after A's
interruption and before the helper's task; the cell after that task; whether A's operation
ended by an interruption; the log; and whether A's fiber and B's fiber ended by an
interruption. The root interrupts B at the end: a B that leased holds its gate. -/
def cancelled (use : Use) (maskedCaller : Bool) : Src NativeOp := eff do
  let pool ← cellOnly
  let log ← Ref.make noRows
  let opExit ← Ref.make (bool false)
  let gH ← Deferred.make .unit .never
  let gB ← Deferred.make .unit .never
  let _ ← fork (Pool.use .nat pool fun _ => Deferred.await gH)
  let fa ← fork ((if maskedCaller then uninterruptible else id)
    (onExitWith (use .nat pool fun r => say log [nat 1, nat 1, r]) fun e =>
      Ref.set opExit (app "causeIsInterrupt" [e])))
  let fb ← fork (use .nat pool fun r =>
    andThen (say log [nat 1, nat 2, r]) (Deferred.await gB))
  let _ ← Deferred.succeed gH unit
  let _ ← withFiber (Action.interrupt fa)
  let ea ← await fa
  let left ← snapshot pool
  let _ ← yieldNow 0
  let _ ← yieldNow 0
  let after ← snapshot pool
  let _ ← withFiber (Action.interrupt fb)
  let eb ← await fb
  let oe ← Ref.get opExit
  let l ← Ref.get log
  return tuple [left, after, oe, l, app "causeIsInterrupt" [ea], app "causeIsInterrupt" [eb]]

#guard verdict (cancelled Pool.use false) = "built" && verdict (cancelled Pool.use true) = "built"
-- **An interruptible caller**: the wait is interrupted, and the withdrawal wins. Nothing is
-- committed to A: its entry leaves, the item stays idle, its operation's exit is an
-- interruption, its body is not entered, and its fiber's exit is an interruption. The helper's
-- selection then finds B: B leases at the stamp 1, and only B's body writes its row.
#guard exitOf (cancelled Pool.use false) = some (.success (.list
  [snap [0] [] [] 1 false 1, snap [] [0] [1] 0 false 2, .bool true, rows [[1, 2, 1]],
    .bool true, .bool true]))
-- **A masked caller**, beside it: the restore is the identity, so A stays enrolled. The
-- commitment is A's: the selection takes A, and A leases at the stamp 1. Its body is entered,
-- and its operation's exit is no interruption: the return runs, and the item is idle again
-- when A's fiber exits. Its fiber's exit is an interruption, when its caller's mask ends. B
-- then leases at the stamp 2.
#guard exitOf (cancelled Pool.use true) = some (.success (.list
  [snap [0] [] [] 1 false 2, snap [] [0] [2] 0 false 3, .bool false, rows [[1, 1, 1], [1, 2, 1]],
    .bool true, .bool true]))
-- The four observations are four values: under the masked caller the operation's exit and the
-- fiber's exit differ, and under the interruptible caller they agree.

-- **Fault: no withdrawal.** A's entry stays after its fiber is gone: two waiters stand where
-- one request waits. The helper's selection at the count 1 takes the entry of nobody, and it
-- resolves a hint that nobody awaits. So the wake is lost: the item stays idle while B waits,
-- and no body runs. Pool's selection is fixed at its count, so the fault costs more here than
-- under Semaphore's live scan.
#guard verdict (cancelled (useOf { withdraws := false }) false) = "built"
#guard exitOf (cancelled (useOf { withdraws := false }) false) = some (.success (.list
  [snap [0] [] [] 2 false 1, snap [0] [] [] 1 false 1, .bool true, rows [], .bool true,
    .bool true]))

/-! ## 3. A late delivery to an old hint after the request waits again

No step of the first profile wakes a waiter beside a held item. So this control posts the wakes
itself: two helpers of the shared `postAll` for the waiter's first hint, while H holds. The
first resumes the waiter: it tries again, does not lease, and enrols again with a fresh hint.
The second is the late delivery: it resolves the old hint, which nobody awaits. -/

/-- The scenario. The answer: the count of waiters after both helpers, whether the waiter's
hint is still the first one, and the waiter's answer after H's return. -/
def rearmed (use : Use) : Src NativeOp := eff do
  let pool ← cellOnly
  let gH ← Deferred.make .unit .never
  let _ ← fork (Pool.use .nat pool fun _ => Deferred.await gH)
  let f ← fork (use .nat pool fun r => succeed r)
  let first ← Ref.get pool
  selectOptionWith (app "get" [field first "waiters", nat 0])
    (succeed (tuple [nat 99, bool true, nat 99])) fun enrolled => eff do
      let _ ← postAll (field first "waiters") unit
      let _ ← postAll (field first "waiters") unit
      let _ ← yieldNow 0
      let second ← Ref.get pool
      selectOptionWith (app "get" [field second "waiters", nat 0])
        (succeed (tuple [nat 98, bool true, nat 98])) fun again => eff do
          let _ ← Deferred.succeed gH unit
          let x ← join f
          return tuple [len (field second "waiters"),
            same (field enrolled "hint") (field again "hint"), x]

#guard verdict (rearmed Pool.use) = "built"
-- After both helpers the waiter is enrolled once, with another hint than its first. H's return
-- then reaches the fresh hint, and the waiter leases the resource 1.
#guard exitOf (rearmed Pool.use) = some (.success (.list [.nat 1, .bool false, .nat 1]))
-- The first helper is fiber 3: it resumes the waiter, fiber 2, which parks again. The second
-- helper is fiber 4: it starts and exits, and it resumes nobody.
#guard (rowsOf (rearmed Pool.use)).take 21 =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 false, .started 2,
   .parked 2, .forked 0 3 true, .scheduled 0, .forked 0 4 true, .scheduled 0, .parked 0, .ran 0,
   .started 3, .resumed 2, .started 2, .parked 2, .exited 3 true, .ran 0, .started 4,
   .exited 4 true]
-- The waiter never yields by its operation budget: each wait is a park.
#guard (rowsOf (rearmed Pool.use)).count (.yielded 2) = 0
-- The ordinary run ends at the truth lane's fuel.
#guard (exitAt 1000 (rearmed Pool.use)).isSome

-- **Fault: one hint for every round.** After the first wake the hint is resolved for good, so
-- each later wait answers at once: the waiter tries again and again without a park, until its
-- operation budget stops it. It keeps its first hint. The ordinary run has no exit at the
-- truth lane's fuel.
#guard verdict (rearmed (useOf { retry := retryOneHintAt })) = "built"
#guard exitOf (rearmed (useOf { retry := retryOneHintAt })) =
  some (.success (.list [.nat 1, .bool true, .nat 1]))
#guard (rowsOf (rearmed (useOf { retry := retryOneHintAt }))).count (.yielded 2) != 0
#guard (exitAt 1000 (rearmed (useOf { retry := retryOneHintAt }))).isNone

/-! ## 4. A holder that is interrupted inside the lease's mask

The first red control of `protectedBy` at Pool (decisions row 276, point 1). A fiber that is
interrupted while it is masked takes the interruption where its mask ends. In `use` the hook is
installed before that point. A lease that holds its own mask ends that mask before the hook: the
interruption lands between them, no return runs, and the lease is lost.

A yield can stand inside a masked region: a yield is no interruption. The first two forms write
one such yield out, after the lease's commit. The last two write none: the forms run under an
operation budget, and the machine's yield at the budget stands there. -/

/-- The lease, and then one yield inside the mask. -/
def leaseThenYield (A : Ty) (pool : TermSrc) (restore : Src NativeOp → Src NativeOp) :
    Src NativeOp :=
  bindWith (Pool.lease A pool restore) fun item => andThen (yieldNow 0) (succeed item)

/-- One region: the protected form, with the yield inside it. -/
def oneRegion : Use := fun A pool body =>
  protectedBy (leaseThenYield A pool) (fun item => Pool.giveBack pool item)
    (fun item => body (field item "resource"))

/-- Two regions: the lease in its own mask, and then the hook. -/
def twoRegions : Use := fun A pool body =>
  bindWith (uninterruptibleMaskWith fun restore => leaseThenYield A pool restore) fun item =>
    onExitWith (body (field item "resource")) fun _ => Pool.giveBack pool item

/-- The item is idle. A leases it and yields inside its mask. A second child requests A's
interruption while A is masked. The answer: the cell while A holds, the cell after the root's
four yields, and whether A's exit is an interruption. -/
def interruptedHolder (use : Use) : Src NativeOp := eff do
  let pool ← cellOnly
  let a ← fork (use .nat pool fun _ => succeed unit)
  let held ← snapshot pool
  let _ ← fork (withFiber (Action.interrupt a))
  let _ ← settle
  let after ← snapshot pool
  let e ← await a
  return tuple [held, after, app "causeIsInterrupt" [e]]

/-- The library's lease in its own mask, and then the hook: two regions, with no yield
written. -/
def leaseThenHook : Use := fun A pool body =>
  bindWith (uninterruptibleMaskWith fun restore => Pool.lease A pool restore) fun item =>
    onExitWith (body (field item "resource")) fun _ => Pool.giveBack pool item

/-- The scenario under an operation budget for A alone. The answer: the cell while the root
first reads it, and the cell after its four yields. -/
def holderUnder (k : Nat) (use : Use) : Src NativeOp := eff do
  let pool ← cellOnly
  let a ← fork (budgeted k (use .nat pool fun _ => succeed unit))
  let held ← snapshot pool
  let _ ← fork (withFiber (Action.interrupt a))
  let _ ← settle
  let after ← snapshot pool
  return tuple [held, after]

/-- The counts of borrowed items at the two readings, on the ordinary tape with three more
flushes. -/
def borrowedUnder (k : Nat) (use : Use) : Option (Nat × Nat) :=
  match (rawOn plain (holderUnder k use)).bind (·.exit) with
  | some (.success (.list [.list (_ :: .list held :: _), .list (_ :: .list after :: _)])) =>
    some (held.length, after.length)
  | _ => none

#guard [interruptedHolder oneRegion, interruptedHolder twoRegions].map verdict =
  ["built", "built"]
-- One region. The interruption waits for the restore site. The hook is installed by then, so
-- the return runs: the item is idle at the end.
#guard exitOf (interruptedHolder oneRegion) = some (.success (.list
  [snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1, .bool true]))
-- Two regions. The interruption lands at the first mask's end, before the hook is installed.
-- No return runs: the item stays borrowed by a fiber that has exited.
#guard exitOf (interruptedHolder twoRegions) = some (.success (.list
  [snap [] [0] [0] 0 false 1, snap [] [0] [0] 0 false 1, .bool true]))
#guard exitOf (interruptedHolder twoRegions) != exitOf (interruptedHolder oneRegion)

-- The library's `use` under the budgets 13 and 30: A yields inside the mask, before its lease
-- step at 13 and after it at 30. The interruption waits, and the return runs: no item is
-- borrowed at the end.
#guard borrowedUnder 13 Pool.use = some (0, 0) && borrowedUnder 30 Pool.use = some (1, 0)
-- The library's lease in its own mask and then the hook, at the same two budgets: the lease is
-- lost.
#guard borrowedUnder 13 leaseThenHook = some (0, 1) && borrowedUnder 30 leaseThenHook = some (1, 1)
-- Measured at each budget from 4 to 54: the two-region form loses the lease at the eighteen
-- budgets from 13 to 30, and at no other. At 12 A yields before the mask, where it is
-- interruptible: nothing is leased. At 31 the two-region form has installed its hook when A
-- yields, so its return runs.
#guard (List.range' 4 51).filter
    (fun k => (borrowedUnder k leaseThenHook).map (·.2) == some 1) = List.range' 13 18
-- The library's form loses it at none of them.
#guard (List.range' 4 51).all fun k => (borrowedUnder k Pool.use).map (·.2) == some 0

/-! ## 5. A waiter that is interrupted under a mask of the form's making

The second red control of `protectedBy` at Pool. A lease that holds its own mask, inside a mask
that a form opens around it, restores to that mask's state: the wait is masked, whatever the
caller. So an interruption does not reach the wait, the withdrawal never runs, and the request
commits a lease after its own interruption. `use` hands the lease the one mask's restore, which
is the caller's state. -/

/-- The lease with its own mask, inside a mask of the form's making. -/
def nested : Use := fun A pool body =>
  uninterruptibleMaskWith fun restore =>
    bindWith (uninterruptibleMaskWith fun inner => Pool.lease A pool inner) fun item =>
      onExitWith (restore (body (field item "resource"))) fun _ => Pool.giveBack pool item

/-- H holds. A waits in a form, and a second child requests A's interruption. H then returns.
The answer: the cell while A waits; the cell after the interrupt's request; the cell at the end;
and whether A's exit is an interruption. -/
def interruptedWaiter (use : Use) : Src NativeOp := eff do
  let pool ← cellOnly
  let gH ← Deferred.make .unit .never
  let _ ← fork (Pool.use .nat pool fun _ => Deferred.await gH)
  let a ← fork (use .nat pool fun _ => succeed unit)
  let waiting ← snapshot pool
  let _ ← fork (withFiber (Action.interrupt a))
  let _ ← settle
  let left ← snapshot pool
  let _ ← Deferred.succeed gH unit
  let _ ← settle
  let after ← snapshot pool
  let e ← await a
  return tuple [waiting, left, after, app "causeIsInterrupt" [e]]

#guard [interruptedWaiter Pool.use, interruptedWaiter nested].map verdict = ["built", "built"]
-- The library's `use`. The wait is interrupted: A's entry leaves, and A commits nothing. After
-- H's return the item is idle, and the next lease's stamp is still 1.
#guard exitOf (interruptedWaiter Pool.use) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1, .bool true]))
-- The nested mask. The wait cannot be interrupted: A's entry stays. After H's return the helper
-- resumes A, and A commits a lease after its own interruption: the next stamp is 2.
#guard exitOf (interruptedWaiter nested) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [0] 1 false 1, snap [0] [] [] 0 false 2, .bool true]))
#guard exitOf (interruptedWaiter nested) != exitOf (interruptedWaiter Pool.use)

/-! ## 6. The returning fiber exits before the dispatch

A borrower waits. The holder's body ends: its hook returns the item, and the holder exits at
once. Its helper is a daemon, and its start is already posted on the holder's dispatcher. -/

/-- The scenario. The answer: whether the holder's exit is an interruption, and the borrower's
answer. The holder is fiber 1 and the borrower fiber 2. -/
def returnerExits (use : Use) : Src NativeOp := eff do
  let pool ← cellOnly
  let gH ← Deferred.make .unit .never
  let fh ← fork (use .nat pool fun _ => Deferred.await gH)
  let ft ← fork (use .nat pool fun r => succeed r)
  let _ ← Deferred.succeed gH unit
  let eh ← await fh
  let x ← join ft
  return tuple [app "causeIsInterrupt" [eh], x]

#guard verdict (returnerExits Pool.use) = "built"
-- The holder, fiber 1, exits with its answer. Its dispatcher then runs the helper, fiber 3,
-- whose selection resumes the borrower.
#guard exitOf (returnerExits Pool.use) = some (.success (.list [.bool false, .nat 1]))
#guard before (.exited 1 true) (.ran 1) (rowsOf (returnerExits Pool.use))
#guard (rowsOf (returnerExits Pool.use)).contains (.forked 1 3 true)

-- **Fault: the helper as a supervised, interruptible child.** The holder's exit interrupts its
-- children. The helper is interrupted before its selection: the wake is lost, the borrower
-- waits for good beside an idle item, and the root has no exit.
#guard verdict (returnerExits (useOf { options := ⟨false, false, .interruptible⟩ })) = "built"
#guard (exitOf (returnerExits (useOf { options := ⟨false, false, .interruptible⟩ }))).isNone
#guard (rowsOf (returnerExits (useOf { options := ⟨false, false, .interruptible⟩ }))).contains
  (.exited 3 false)

/-! ## 7. The receiver's continuation that grows

The helper's task runs the resumed borrower: its next attempt, then its body, and then its
return, under the task's own budget (decisions rows 226 and 238). Here the borrower's body is a
loop of `n` steps. The measure is the least fuel at which the flush of the helper's task ends
the root.

**No bound is claimed.** The numbers are measured on this program at these lengths. -/

/-- A borrower whose body runs `n` steps; the root opens the holder's gate, and joins it. -/
def grows (n : Nat) : Src NativeOp := eff do
  let pool ← cellOnly
  let steps ← Ref.make (nat 0)
  let gH ← Deferred.make .unit .never
  let _ ← fork (Pool.use .nat pool fun _ => Deferred.await gH)
  let f ← fork (Pool.use .nat pool fun r => andThen
    (forRange (nat 0) (nat n) fun _ => Ref.updateWith steps fun c => app "succ" [c])
    (succeed r))
  let _ ← Deferred.succeed gH unit
  let x ← join f
  let c ← Ref.get steps
  return tuple [x, c]

/-- The root's exit after one flush at a fuel, and then after five more flushes at the ample
fuel. The root is evaluated at the ample fuel first: it parks at its join, with the helper's
start posted. -/
def flushAt (b : Api.Built) (budget : Nat) : Bool × Bool :=
  let ample : Api.Budget := { fuel := fuel, compileFuel := fuel }
  let evaluated := (Run.open b "traces" ample).control Api.evaluate
  let one := ({ evaluated with budget := { fuel := budget, compileFuel := fuel } } : Run).control
    Api.flush
  let more := (List.range 5).foldl (fun (s : Run) _ => s.control Api.flush)
    ({ one with budget := ample } : Run)
  (one.exit.isSome, more.exit.isSome)

/-- `flushAt` on a source's built program. -/
def afterFlush (src : Src NativeOp) (budget : Nat) : Option (Bool × Bool) :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => flushAt b budget

/-- The lengths, each with the least fuel of the delivery's flush that was measured for it. -/
def measured : List (Nat × Nat) :=
  [(0, 61), (1, 64), (2, 67), (4, 73), (8, 85), (16, 109), (32, 157)]

-- Each program builds, and it answers its resource and its count of steps.
#guard measured.all fun (n, _) =>
  exitOf (grows n) == some (.success (.list [.nat 1, .nat n]))
-- At the measured fuel the flush ends the root. The empty body is the control: 61.
#guard measured.all fun (n, least) => afterFlush (grows n) least == some (true, true)
-- At one less it does not. And five more flushes at the ample fuel do not end it either: the
-- cut inside the dispatch lost the work that remained, and a later flush is no resumption.
-- Decisions row 226 excludes that cut from the first profile, so this is the excluded case,
-- and no fault of the wake.
#guard measured.all fun (n, least) => afterFlush (grows n) (least - 1) == some (false, false)
-- The measured fuel grows with the body: three for each step, at these lengths.
#guard measured.all fun (n, least) => least == 61 + 3 * n

/-! ## 8. The protected lease under a masked caller

Under a masked caller the mask's restore is the identity: the wait is not interrupted, the
request stays enrolled, and it leases. The body runs inside the caller's mask, the return runs
at its exit, and the fiber is interrupted when its caller's mask ends.

The red control restores with `interruptible`, whatever its caller, so its wait is interrupted
under the masked caller. -/

/-- A form that restores with `interruptible`, whatever its caller: a stand-in for the mask. -/
def standIn : Use := fun A pool body =>
  uninterruptible
    (bindWith (Pool.lease A pool interruptible) fun item =>
      onExitWith (interruptible (body (field item "resource"))) fun _ => Pool.giveBack pool item)

/-- H holds. A child asks in a form, under `uninterruptible`: it waits. A second child requests
its interruption. H then returns. The body writes the row `[1, 1, resource]`. The answer: the
cell after the interrupt's request, the log, whether the child's exit is an interruption, and
the cell at the end. -/
def maskedCallerWith (use : Use) : Src NativeOp := eff do
  let pool ← cellOnly
  let log ← Ref.make noRows
  let gH ← Deferred.make .unit .never
  let _ ← fork (Pool.use .nat pool fun _ => Deferred.await gH)
  let f ← fork (uninterruptible (use .nat pool fun r => say log [nat 1, nat 1, r]))
  let stop ← fork (withFiber (Action.interrupt f))
  let registered ← snapshot pool
  let _ ← Deferred.succeed gH unit
  let e ← await f
  let _ ← await stop
  let l ← Ref.get log
  let after ← snapshot pool
  return tuple [registered, l, app "causeIsInterrupt" [e], after]

/-- The masked caller over the library's `use`. -/
def maskedCaller : Src NativeOp := maskedCallerWith Pool.use

#guard verdict maskedCaller = "built"
-- With the mask that restores: the waiter stays enrolled after the interrupt's request. After
-- H's return the body runs, and it writes its row. The child's exit is an interruption, and the
-- return ran: the item is idle at the end, and nobody waits.
#guard exitOf maskedCaller = some (.success (.list
  [snap [] [0] [0] 1 false 1, rows [[1, 1, 1]], .bool true, snap [0] [] [] 0 false 2]))
-- The ordinary run gives the same answer at the truth lane's fuel.
#guard exitAt 1000 maskedCaller = exitOf maskedCaller
-- Red control: the stand-in restores with `interruptible`. Its wait is interrupted under the
-- masked caller: the waiter withdraws, and its body never runs.
#guard verdict (maskedCallerWith standIn) = "built"
#guard exitOf (maskedCallerWith standIn) = some (.success (.list
  [snap [] [0] [0] 0 false 1, rows [], .bool true, snap [0] [] [] 0 false 1]))
-- H is fiber 1, the child fiber 2 and its interruptor fiber 3. The helper is fiber 4: it
-- resumes the child, which exits by the interruption only then, and the interruptor after it.
#guard rowsOf maskedCaller =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 false, .started 2,
   .parked 2, .forked 0 3 false, .started 3, .interrupted 2, .parked 3, .resumed 1, .started 1,
   .forked 1 4 true, .scheduled 1, .exited 1 true, .parked 0, .ran 1, .started 4, .resumed 2,
   .started 2, .exited 2 false, .resumed 3, .started 3, .exited 3 true, .resumed 0, .started 0,
   .exited 0 true, .exited 4 true]

/-! ## 9. A borrow at a closing pool, and a borrow at a closed pool under a masked caller

Decisions row 279, point 2: a borrow at a closed pool interrupts the borrower itself, and its
body does not run. The answer is a failure whose cause is the interruption of the borrower's
own fiber. It is no delivery of an interruption, so a mask does not hold it back.

The first control is the closing pool of `Test/Program/PoolPublic.lean`, with the cell's own
fields read: the items' records and the idle list, before the close and after the late
borrower's exit. The second is the closed pool with the late borrower under `uninterruptible`. -/

/-- H holds, and W waits. L awaits W's exit, and then it borrows: the close has begun by then,
and H still holds. A fourth fiber awaits L's exit, reads the cell, and opens H's gate. The
answer: the items' records before the close and after L's exit; the idle stamps at both
points; the waiters' count at both points; and whether L's exit is an interruption. -/
def closingCell : Src NativeOp := eff do
  let log ← Ref.make noRows
  let counter ← Ref.make (nat 0)
  let gH ← Deferred.make .unit .never
  let first ← Ref.make (Pool.initial .nat [nat 1])
  let seen ← Ref.make (Pool.initial .nat [nat 1])
  let inside ← scope (eff do
    let pool ← Pool.make .nat 1 (acquire counter log)
    let _ ← fork (Pool.use .nat pool (holding log 9 (Deferred.await gH)))
    let w ← fork (Pool.use .nat pool (holding log 1 (succeed unit)))
    let late ← fork (eff do
      let _ ← await w
      Pool.use .nat pool (holding log 5 (succeed unit)))
    let _ ← fork (eff do
      let _ ← await late
      let s ← Ref.get pool
      let _ ← Ref.set seen s
      Deferred.succeed gH unit)
    let s ← Ref.get pool
    let _ ← Ref.set first s
    return late)
  let el ← await inside
  let before ← Ref.get first
  let after ← Ref.get seen
  return tuple [field before "items", field after "items", field before "available",
    field after "available", len (field before "waiters"), len (field after "waiters"),
    field after "closing", app "causeIsInterrupt" [el]]

/-- The pool's scope closes with no borrower. Then L borrows under `uninterruptible`. The
answer: L's exit, and the log. L is fiber 1. -/
def closedMasked : Src NativeOp := eff do
  let log ← Ref.make noRows
  let counter ← Ref.make (nat 0)
  let pool ← scope (Pool.make .nat 1 (acquire counter log))
  let late ← fork (uninterruptible (Pool.use .nat pool (holding log 5 (succeed unit))))
  let e ← await late
  let l ← Ref.get log
  return tuple [e, l]

/-- H's item as its lease 0 holds it: the record of the stamp 0 at the resource 1. -/
def heldItem : Val :=
  .ctor 0 [.list [.str "borrowed", .str "lease", .str "resource", .str "stamp"],
    .list [.bool true, .nat 0, .nat 1, .nat 0]]

#guard [closingCell, closedMasked].map verdict = ["built", "built"]
-- **A borrow at a closing pool, while a holder holds.** Every item's record is as it was:
-- H's lease still holds the item, at the stamp 0. The idle list is as it was: empty. One
-- request waits before the close, which is W. One waits after L's exit, which is the closer:
-- the close's helper took W, and L's request left no entry. The pool is closing, and L's exit
-- is an interruption.
#guard exitOf closingCell = some (.success (.list
  [.list [heldItem], .list [heldItem], .list [], .list [], .nat 1, .nat 1, .bool true,
    .bool true]))
-- The refusal is the lease step's own: at a closing pool it removes the request's entry, and
-- it changes nothing else (`lease_closed`, `src/Effect4/Laws/Library/Pool/Profile.lean`).

-- **A borrow at a closed pool, under a masked caller.** L is fiber 1, and it runs under
-- `uninterruptible`. Its exit is still the interruption of its own fiber: the answer is a
-- failure with that cause, and no delivery of an interruption, so the mask does not hold it
-- back. Its body did not run: the log holds the finalizer's row alone.
#guard exitOf closedMasked = some (.success (.list
  [Val.exitErr (Cause.interrupt (some ⟨1⟩)), rows [[9, 1]]]))
-- The same exit as with no mask (`Test/Program/PoolPublic.lean`, the closed pool).
#guard (exitOf closedMasked).map (fun
    | .success (.list (e :: _)) => e == Val.exitErr (Cause.interrupt (some ⟨1⟩))
    | _ => false) = some true

end Test.Program.PoolTraces
