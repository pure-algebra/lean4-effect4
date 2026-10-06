import Test.Program.QueueScenarios
import Effect4.Program.Authoring.Mask

/-!
# The Queue's acceptance traces (decisions rows 221, 222, 226, 238 and 240)

Decisions row 221 names three acceptance traces of the waiting wrapper, and the wrapper's design
adds four (`docs/research/2026-10-05-claude-lead/waiting-design.md`, F5, F7 and proposal 5). This
battery runs the seven on the Lean machine, over the library's operations
(`src/Effect4/Modules/Queue/Ops.lean`). Each has its positive control, and a fault that fails
the promised property.

| # | The trace | The registry's open part that it is a finite control of |
| --- | --- | --- |
| 1 | a notification before the await | `wait-registration-no-gap` |
| 2 | a cancellation after the selection, before the delivery | `waiting-request-obligation-preserved` |
| 3 | a late delivery to an old hint after a second wait | `posted-task-decision-preserves` |
| 4 | a blocked offerer, cancelled before its message is accepted | `queue-expansion-agrees` |
| 5 | a blocked offerer, cancelled after its message is accepted | `queue-expansion-agrees` |
| 6 | the signalling fiber exits before the dispatch | `posted-wake-profile-agrees` |
| 7 | the receiver's continuation that grows | `embedded-budget-sufficient` |

The last part is decisions row 226's, under requirement R12: the embedded budget covers the
registration, the cleanup and the selected delivery, and a cut inside the operation is excluded.

**A fault is a variant of the Queue's part of an operation** (`Variant`): another delivery of a
signal, a withdrawal that posts nothing, no withdrawal, one hint for every round, or a
withdrawal that takes a message back. The variant with no change is the library's operation,
tree for tree. Each faulty program builds: the checker types it. So each fault fails the
promised property, and not typing alone.

**A cancellation control records four observations apart** (decisions row 222): the commitment,
the operation's exit, the entry of the caller's continuation, and the fiber's exit. A child
fiber runs the operation under a hook that writes the operation's exit, and then one more step
that writes a mark. The root reads the cell, the hook's write, the mark and the child's exit.

**The settings of every run.** The tape is the ordinary one, the root evaluated and then one
flush, with three more flushes. Trace 1 has tapes of its own: it fires one dispatcher at a
time. The fuel is 20000. A child is forked with the default options: it starts at once.

Placement. Every guard is one run on one schedule, a finite control of the open part that its
trace names. None proves delivery, a cancellation law, a bound or liveness, and none is a host
run. Trace 1's programs are raw: an operation budget is a reserved service, and the checker
refuses its provision.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueTraces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios (Ops library mk verdict exitOf exitAt fuel)
open Effect4.Modules

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

/-- The ordinary tape, with three more flushes. -/
def plain : List Api.Decision := [Api.evaluate, Api.flush, Api.flush, Api.flush, Api.flush]

/-- A built source's run on a tape, through the checked session. -/
def runOn (tape : List Api.Decision) (src : Src NativeOp) : Option Run :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b =>
    (Run.open b "traces" { fuel := fuel, compileFuel := fuel }).play (Rows.tape tape)

/-- The rows of a built source's ordinary run. -/
def rowsOf (src : Src NativeOp) : List Row :=
  ((runOn plain src).map fun r => r.machine.trace.filterMap rowOf).getD []

/-- Whether one row stands before another in a list of rows. -/
def before (first second : Row) (rows : List Row) : Bool :=
  match rows.idxOf? first, rows.idxOf? second with
  | some i, some j => decide (i < j)
  | _, _ => false

/-! ## The variants of the Queue's part

A variant changes the Queue's part of `take` and of `offer`, and nothing of the wrapper. The
library's operation is the variant with no change. -/

/-- The knobs of a variant. Each default is the library's. -/
structure Variant where
  /-- How a step's signals are delivered. -/
  post : TermSrc → TermSrc → Src NativeOp := postAll
  /-- Whether a withdrawal posts the wake that its step names. -/
  withdrawalPosts : Bool := true
  /-- Whether an interrupted wait withdraws its request. -/
  withdraws : Bool := true
  /-- The wrapper of `take`. -/
  retry : Ty → String → Waiter → Src NativeOp := waitRetry
  /-- The term of an offer's withdrawal. -/
  withdrawOffer : Ty → TermSrc → TermSrc → TermSrc := Queue.withdrawOffer

/-- A withdrawal under a variant: its step, and its posts. -/
def withdrawalOf (v : Variant) (q : TermSrc) (step : TermSrc → TermSrc) : Src NativeOp :=
  if v.withdraws then
    bindWith (Ref.modifyWith q step) fun woken =>
      if v.withdrawalPosts then v.post woken unit else succeed (nat 0)
  else succeed (nat 0)

/-- `take` under a variant. -/
def takeOf (v : Variant) (A : Ty) (q : TermSrc) : Src NativeOp :=
  v.retry A "queue: the loop ended without a message"
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (Queue.takeStep A id hint)) fun reply =>
          andThen (v.post (tupleAt reply 1) (bool true))
            (andThen (v.post (tupleAt reply 2) unit)
              (selectOptionWith (tupleAt reply 0) wait done))
      withdraw := fun id => withdrawalOf v q (Queue.withdrawTake A id) }

/-- `offer` under a variant. -/
def offerOf (v : Variant) (A : Ty) (q message : TermSrc) : Src NativeOp :=
  waitAnswer
    { hint := .bool
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (Queue.offerStep A id hint message)) fun reply =>
          andThen (v.post (tupleAt reply 1) unit)
            (selectOptionWith (tupleAt reply 0) wait done)
      withdraw := fun id => withdrawalOf v q (v.withdrawOffer A id) }

/-- The operations of a variant. -/
def opsOf (v : Variant) : Ops := { take := takeOf v, offer := offerOf v, size := Queue.size }

-- The variant with no change is the library's operation, tree for tree.
#guard elaborate (bindName "q" (Queue.bounded .nat 2) fun q => takeOf {} .nat q) ==
  elaborate (bindName "q" (Queue.bounded .nat 2) fun q => Queue.take .nat q)
#guard elaborate (bindName "q" (Queue.bounded .nat 2) fun q => offerOf {} .nat q (nat 1)) ==
  elaborate (bindName "q" (Queue.bounded .nat 2) fun q => Queue.offer .nat q (nat 1))
#guard (elaborate (bindName "q" (Queue.bounded .nat 2) fun q => takeOf {} .nat q)).toOption.isSome

/-- One helper for each request, with other fork options than the posted helper's. -/
def postWith (options : Effect4.Supervision.ForkOptions) (requests answer : TermSrc) :
    Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOptionWith (app "get" [requests, i]) (succeed unit) fun request =>
        andThen
          (withFiber (Action.fork (Deferred.succeed (field request "hint") answer) options))
          (succeed unit)
      step := fun i _ => app "succ" [i] }

-- With the posted helper's options it is `postAll`, tree for tree.
#guard elaborate (bindName "xs" (succeed nilT) fun xs => postWith posted xs unit) ==
  elaborate (bindName "xs" (succeed nilT) fun xs => postAll xs unit)

/-- **The inline delivery**: each hint is resolved in the signalling step's own fiber, by an
ordinary `Deferred.succeed`, with no helper. -/
def postInline (requests answer : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOptionWith (app "get" [requests, i]) (succeed unit) fun request =>
        andThen (Deferred.succeed (field request "hint") answer) (succeed unit)
      step := fun i _ => app "succ" [i] }

/-- **One hint for every round**: `waitRetry` with the hint allocated once, before the loop. -/
def retryOneHint (result : Ty) (ended : String) (w : Waiter) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
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

/-- **A withdrawal that takes a message back**: the offer's withdrawal, which also drops the
newest buffered message. -/
def takesBack (_A : Ty) (id s : TermSrc) : TermSrc :=
  app "pair" [Queue.wake (field s "takers") (field s "msgs"),
    recordSet (recordSet s "offers" (Queue.removeOffer (field s "offers") id)) "msgs"
      (app "take" [field s "msgs", app "sub" [len (field s "msgs"), nat 1]])]

/-! ## The pieces of a control -/

/-- The empty list of numbers. -/
def noNumbers : TermSrc := app "take" [app "cons" [nat 0, nilT], nat 0]

/-- A mark joins a log. -/
def mark (log x : TermSrc) : Src NativeOp := Ref.updateWith log fun l => snoc l x

/-- **An operation under observation** (decisions row 222): the hook writes whether the
operation's exit is an interruption, and the step after the operation writes its answer as a
mark. So the operation's exit and the entry of the caller's continuation are two cells. -/
def observed (operation : Src NativeOp) (opExit entered : TermSrc) : Src NativeOp :=
  bindWith (onExitWith operation fun e => Ref.set opExit (app "causeIsInterrupt" [e]))
    fun answer => mark entered answer

/-! ## 1. A notification before the await

The hint resolves only in the helper's task. So the signalling fiber runs none of the
receiver's code, and a request that is notified before it awaits loses nothing. -/

/-- A taker marks its message, and the root marks `101` when its offer returns. -/
def marks (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let log ← Ref.make noNumbers
  let f ← fork (eff do
    let x ← ops.take .nat q
    mark log x)
  let _ ← ops.offer .nat q (nat 7)
  let _ ← mark log (nat 101)
  let _ ← join f
  let l ← Ref.get log
  return l

#guard verdict (marks library) = "built" && verdict (marks (opsOf { post := postInline })) = "built"
-- The posted delivery: the offer returns, and the taker goes on after it, in the helper's task.
#guard exitOf (marks library) = some (.success (.list [.nat 101, .nat 7]))
-- **An ordinary `Deferred` keeps its inline delivery.** With the inline variant the taker's
-- attempt and its continuation run inside the offer: its mark comes first. So the order above
-- is the helper's, and no change of `Deferred`.
#guard exitOf (marks (opsOf { post := postInline })) = some (.success (.list [.nat 7, .nat 101]))

/-! ### The await before the task, and the await after it

An operation budget stops the taker between its registration and its await. The root then
offers: its step names the taker, and it posts the helper. Two tapes follow. On the first the
taker's dispatcher fires before the root's: the taker awaits and parks, and the helper's task
then resumes it. On the second the root's dispatcher fires first: the helper resolves the hint,
and the taker's await then answers at once. On both the taker's next attempt follows the
helper's task, and it takes the message.

These programs are raw: the budget is the reserved reference `Env.maxOpsKey`, and the checker
refuses its provision. `Api.replay` is the unchecked run. -/

/-- A body under an operation budget: the fiber yields before its operation `k` of an entry. -/
def budgeted (k : Nat) (body : Src NativeOp) : Src NativeOp :=
  provideService Env.maxOpsKey (nat k) body

/-- A taker under an operation budget; the root offers, and joins it. -/
def notified (k : Nat) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (budgeted k (Queue.take .nat q))
  let _ ← Queue.offer .nat q (nat 7)
  let x ← join f
  return x

/-- The raw run of a source on a tape. -/
def rawOn (tape : List Api.Decision) (src : Src NativeOp) : Option Api.Inspection :=
  (elaborateModule (mk src)).toOption.map fun p => Api.replay p fuel tape

/-- The buffer's length and the count of waiting takers, in the queue's cell: the first cell
that a run makes. -/
def cellOf (r : Api.Inspection) : Option (Nat × Nat) :=
  (r.machine.state.refs[0]?).bind fun cell =>
    match Machine.Record.read false cell "msgs", Machine.Record.read false cell "takers" with
    | some (.list messages), some (.list takers) => some (messages.length, takers.length)
    | _, _ => none

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
evaluation the taker has yielded once, it is enrolled, and the offered message is buffered. -/
def stopsBetween (k : Nat) : Bool :=
  match rawOn [Api.evaluate] (notified k) with
  | some r =>
    (r.machine.trace.filterMap rowOf).count (.yielded 1) == 1 && cellOf r == some (1, 1)
  | none => false

-- The checker refuses the budget's provision, so the programs are raw.
#guard verdict (notified 25) = "typing: serviceUnknown"
-- The budgets that stop the taker between its registration and its await: 21 to 33. Below 21
-- the taker yields before its step, and from 34 it reaches its await with no yield.
#guard (List.range 40).filter stopsBetween = List.range' 21 13

-- At each such budget, on both tapes: no attempt runs before the helper's task and the taker's
-- resume have both run. After the first of the two dispatchers the message is still buffered
-- and the taker is still enrolled. At the end the taker has taken the message, and the root has
-- exited with it.
#guard (List.range' 21 13).all fun k =>
  [awaitFirst, taskFirst].all fun tape =>
    (stages tape (notified k)).take 2 == [(some (1, 1), false), (some (1, 1), false)] &&
      (stages tape (notified k)).drop 3 == [(some (0, 0), true)] &&
      ((rawOn tape (notified k)).bind (·.exit)) == some (.success (.nat 7))
-- On the first tape the helper's task resumes the parked taker, and the taker's attempt runs
-- inside that task: the message has left the buffer when the root's dispatcher has fired.
#guard (List.range' 21 13).all fun k =>
  ((stages awaitFirst (notified k))[2]?).map (·.1) == some (some (0, 0))

/-- The rows of a raw run on a tape. -/
def rawRows (tape : List Api.Decision) (src : Src NativeOp) : List Row :=
  ((rawOn tape src).map fun r => r.machine.trace.filterMap rowOf).getD []

-- The await before the task, at the budget 25. The taker's dispatcher runs: the taker parks at
-- its hint. Then the root's dispatcher runs the helper, fiber 2, which resumes the taker.
#guard (rawRows awaitFirst (notified 25)).take 16 =
  [.started 0, .forked 0 1 false, .started 1, .yielded 1, .parked 1, .forked 0 2 true,
   .scheduled 0, .parked 0, .ran 1, .resumed 1, .started 1, .parked 1, .ran 0, .started 2,
   .resumed 1, .started 1]
-- The task before the await. The helper runs and exits, and it resumes nobody. The taker's
-- dispatcher then runs: the taker's await answers at once, so no park follows its resume. Its
-- next row is the budget's second yield, inside the attempt that takes the message.
#guard (rawRows taskFirst (notified 25)).take 16 =
  [.started 0, .forked 0 1 false, .started 1, .yielded 1, .parked 1, .forked 0 2 true,
   .scheduled 0, .parked 0, .ran 0, .started 2, .exited 2 true, .ran 1, .resumed 1, .started 1,
   .yielded 1, .parked 1]
-- Red control of the two tapes: they are two schedules.
#guard rawRows awaitFirst (notified 25) != rawRows taskFirst (notified 25)

/-! ## 2. A cancellation after the selection and before the delivery

Two takers wait, A and then B. An offer buffers a message: its step selects A, and it posts A's
wake. The root interrupts A before the helper's task runs. -/

/-- The scenario, with A under either caller. The answer: the buffer's size, the count of
waiting takers, whether A's operation ended by an interruption, the count of A's continuation's
marks, and whether A's fiber and B's fiber ended by an interruption. The root interrupts B at
the end: a B that the queue served has exited by then. -/
def selected (ops : Ops) (maskedCaller : Bool) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let opExit ← Ref.make (bool false)
  let entered ← Ref.make noNumbers
  let fa ← fork ((if maskedCaller then uninterruptible else id)
    (observed (ops.take .nat q) opExit entered))
  let fb ← fork (ops.take .nat q)
  let _ ← ops.offer .nat q (nat 7)
  let _ ← withFiber (Action.interrupt fa)
  let ea ← await fa
  let _ ← yieldNow 0
  let _ ← yieldNow 0
  let n ← ops.size .nat q
  let s ← Ref.get q
  let _ ← withFiber (Action.interrupt fb)
  let eb ← await fb
  let oe ← Ref.get opExit
  let en ← Ref.get entered
  return tuple [n, len (field s "takers"), oe, len en, app "causeIsInterrupt" [ea],
    app "causeIsInterrupt" [eb]]

#guard verdict (selected library false) = "built" && verdict (selected library true) = "built"
-- **An interruptible caller**: the wait is interrupted, and the withdrawal wins. Nothing is
-- committed to A: its operation's exit is an interruption, its continuation is not entered,
-- and its fiber's exit is an interruption. The withdrawal passes the signal on: B takes the
-- message, so the buffer is empty, no taker waits, and B's fiber ended with a message.
#guard exitOf (selected library false) =
  some (.success (.list [.nat 0, .nat 0, .bool true, .nat 0, .bool true, .bool false]))
-- **A masked caller**, beside it: the restore is the identity, so A stays registered. The
-- commitment is A's: it takes the message. Its operation's exit is no interruption, and its
-- continuation is entered once. Its fiber's exit is an interruption, when its caller's mask
-- ends. B is never served: it waits until the root interrupts it.
#guard exitOf (selected library true) =
  some (.success (.list [.nat 0, .nat 1, .bool false, .nat 1, .bool true, .bool true]))
-- The four observations are four values: under the masked caller the operation's exit and the
-- fiber's exit differ, and under the interruptible caller they agree.

-- The withdrawal's helper is forked by A, fiber 1, and A exits before its dispatcher runs it.
#guard before (.exited 1 false) (.ran 1) (rowsOf (selected library false))

-- **Fault: a withdrawal that posts nothing.** A's withdrawal names B, and nobody wakes it: the
-- message stays in the buffer while B waits, until the root interrupts B.
#guard verdict (selected (opsOf { withdrawalPosts := false }) false) = "built"
#guard exitOf (selected (opsOf { withdrawalPosts := false }) false) =
  some (.success (.list [.nat 1, .nat 1, .bool true, .nat 0, .bool true, .bool true]))

/-! ## 3. A late delivery to an old hint after the request waits again

In the first profile no step wakes a taker that finds nothing. So this control posts the wakes
itself: two helpers for the taker's hint, while the buffer is empty. The first resumes the
taker: it tries again, takes nothing, and waits again with a fresh hint. The second is the late
delivery: it resolves the old hint, which nobody awaits. -/

/-- The scenario. The answer: the count of waiting takers after both helpers, whether the
taker's hint is still the first one, the buffer's size, and the taker's message after an offer. -/
def rearmed (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (ops.take .nat q)
  let first ← Ref.get q
  selectOptionWith (app "get" [field first "takers", nat 0])
    (succeed (tuple [nat 99, bool true, nat 99, nat 99])) fun enrolled => eff do
      let _ ← postAll (field first "takers") unit
      let _ ← postAll (field first "takers") unit
      let _ ← yieldNow 0
      let second ← Ref.get q
      selectOptionWith (app "get" [field second "takers", nat 0])
        (succeed (tuple [nat 98, bool true, nat 98, nat 98])) fun again => eff do
          let n ← Queue.size .nat q
          let _ ← ops.offer .nat q (nat 7)
          let x ← join f
          return tuple [len (field second "takers"),
            same (field enrolled "hint") (field again "hint"), n, x]

#guard verdict (rearmed library) = "built"
-- After both helpers the taker is enrolled once, with another hint than its first. Nothing is
-- buffered. The offer's wake then reaches the fresh hint, and the taker takes the message.
#guard exitOf (rearmed library) =
  some (.success (.list [.nat 1, .bool false, .nat 0, .nat 7]))
-- The first helper is fiber 2: it resumes the taker, fiber 1, which parks again. The second
-- helper is fiber 3: it starts and exits, and it resumes nobody.
#guard (rowsOf (rearmed library)).take 18 =
  [.started 0, .forked 0 1 false, .started 1, .parked 1, .forked 0 2 true, .scheduled 0,
   .forked 0 3 true, .scheduled 0, .parked 0, .ran 0, .started 2, .resumed 1, .started 1,
   .parked 1, .exited 2 true, .ran 0, .started 3, .exited 3 true]
-- The taker never yields by its operation budget: each wait is a park.
#guard (rowsOf (rearmed library)).count (.yielded 1) = 0
-- The ordinary run ends at the truth lane's fuel.
#guard (exitAt 1000 (rearmed library)).isSome

-- **Fault: one hint for every round.** After the first wake the hint is resolved for good, so
-- each later wait answers at once: the taker tries again and again without a park. It keeps
-- its first hint. Its operation budget stops it at last, the offer then buffers a message, and
-- a later attempt takes it. The ordinary run has no exit at the truth lane's fuel.
#guard verdict (rearmed (opsOf { retry := retryOneHint })) = "built"
#guard exitOf (rearmed (opsOf { retry := retryOneHint })) =
  some (.success (.list [.nat 1, .bool true, .nat 0, .nat 7]))
#guard (rowsOf (rearmed (opsOf { retry := retryOneHint }))).count (.yielded 1) != 0
#guard (exitAt 1000 (rearmed (opsOf { retry := retryOneHint }))).isNone

/-! ## 4. A blocked offerer that is cancelled before any step accepts its message

Capacity one. A first offer is accepted. A second offerer waits, and the root interrupts it. -/

/-- The scenario. The answer: the pending offers before and after the interrupt, the message
that a take then gets, what a poll finds after it, a later offer's answer and the message that
a last poll finds, whether the offerer's operation ended by an interruption, the count of its
continuation's marks, and whether its fiber ended by an interruption. -/
def cancelledPending (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let opExit ← Ref.make (bool false)
  let entered ← Ref.make (app "take" [app "cons" [bool true, nilT], nat 0])
  let _ ← ops.offer .nat q (nat 1)
  let f ← fork (observed (ops.offer .nat q (nat 2)) opExit entered)
  let pending ← Ref.get q
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let left ← Ref.get q
  let x ← ops.take .nat q
  let _ ← yieldNow 0
  let y ← Queue.poll .nat q
  let later ← ops.offer .nat q (nat 3)
  let z ← Queue.poll .nat q
  let oe ← Ref.get opExit
  let en ← Ref.get entered
  return tuple [len (field pending "offers"), len (field left "offers"), x, y, later, z, oe,
    len en, app "causeIsInterrupt" [e]]

#guard verdict (cancelledPending library) = "built"
-- The withdrawal removes the pending offer. Nothing of it is committed: the take gets the
-- first message, a poll then finds nothing, and a later offer is accepted and polled. The
-- operation's exit is an interruption, its continuation is not entered, and the fiber's exit
-- is an interruption.
#guard exitOf (cancelledPending library) =
  some (.success (.list [.nat 1, .nat 0, .nat 1, .none, .bool true, .some (.nat 3),
    .bool true, .nat 0, .bool true]))

-- **Fault: no withdrawal.** The offer stays pending after its offerer is gone. The take that
-- frees room accepts it: the poll finds the message 2 of a cancelled request.
#guard verdict (cancelledPending (opsOf { withdraws := false })) = "built"
#guard exitOf (cancelledPending (opsOf { withdraws := false })) =
  some (.success (.list [.nat 1, .nat 1, .nat 1, .some (.nat 2), .bool true, .some (.nat 3),
    .bool true, .nat 0, .bool true]))

/-! ## 5. A blocked offerer that is cancelled after a step accepted its message

Capacity one. A first offer is accepted, and a second offerer waits. The root's take frees
room: its step accepts the second offer, and it posts the offerer's answer. The root interrupts
the offerer before the helper's task runs. -/

/-- The scenario, with or without the interrupt. The answer: the message that the take gets,
the buffer's size and the pending offers after that take, what a poll finds at the end, whether
the offerer's operation ended by an interruption, its continuation's marks, and whether its
fiber ended by an interruption. A mark is `1` for the answer `true`. -/
def cancelledAccepted (ops : Ops) (cancel : Bool) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let opExit ← Ref.make (bool false)
  let entered ← Ref.make noNumbers
  let _ ← ops.offer .nat q (nat 1)
  let f ← fork (eff do
    let ok ← onExitWith (ops.offer .nat q (nat 2)) fun e =>
      Ref.set opExit (app "causeIsInterrupt" [e])
    mark entered (ifT ok (nat 1) (nat 0)))
  let x ← ops.take .nat q
  let accepted ← Ref.get q
  let _ ← (if cancel then withFiber (Action.interrupt f) else succeed unit)
  let e ← await f
  let _ ← yieldNow 0
  let y ← Queue.poll .nat q
  let oe ← Ref.get opExit
  let en ← Ref.get entered
  return tuple [x, len (field accepted "msgs"), len (field accepted "offers"), y, oe, en,
    app "causeIsInterrupt" [e]]

#guard verdict (cancelledAccepted library true) = "built"
-- **The commitment stays.** The take's step accepted the message: the buffer holds it, and no
-- offer is pending. The offerer is interrupted before it reads its answer: its operation's
-- exit is an interruption, its continuation is not entered, and its fiber's exit is an
-- interruption. The message stays accepted: the poll finds it.
#guard exitOf (cancelledAccepted library true) =
  some (.success (.list [.nat 1, .nat 1, .nat 0, .some (.nat 2), .bool true, .list [],
    .bool true]))
-- **The control: the offerer that is not cancelled.** The helper delivers `true`: the
-- continuation's mark is `1`, and neither exit is an interruption.
#guard exitOf (cancelledAccepted library false) =
  some (.success (.list [.nat 1, .nat 1, .nat 0, .some (.nat 2), .bool false, .list [.nat 1],
    .bool false]))
-- The helper of the answer is fiber 2. It runs after the offerer, fiber 1, has exited, and it
-- resumes nobody.
#guard before (.exited 1 false) (.started 2) (rowsOf (cancelledAccepted library true))

-- **Fault: a withdrawal that takes the message back.** The accepted message leaves the buffer
-- with its cancelled offerer: the poll finds nothing.
#guard verdict (cancelledAccepted (opsOf { withdrawOffer := takesBack }) true) = "built"
#guard exitOf (cancelledAccepted (opsOf { withdrawOffer := takesBack }) true) =
  some (.success (.list [.nat 1, .nat 1, .nat 0, .none, .bool true, .list [], .bool true]))

/-! ## 6. The signalling fiber exits before the dispatch

A taker waits. A second fiber offers and exits at once. Its helper is a daemon, and its start is
already posted on the offerer's dispatcher. -/

/-- The scenario. The answer: whether the offerer's exit is an interruption, and the taker's
message. -/
def signallerExits (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let ft ← fork (ops.take .nat q)
  let fs ← fork (ops.offer .nat q (nat 7))
  let es ← await fs
  let x ← join ft
  return tuple [app "causeIsInterrupt" [es], x]

#guard verdict (signallerExits library) = "built"
-- The offerer, fiber 2, exits with its answer. Its dispatcher then runs the helper, fiber 3,
-- which resumes the taker.
#guard exitOf (signallerExits library) = some (.success (.list [.bool false, .nat 7]))
#guard before (.exited 2 true) (.ran 2) (rowsOf (signallerExits library))
#guard (rowsOf (signallerExits library)).contains (.forked 2 3 true)

-- **Fault: the helper as a supervised, interruptible child.** The offerer's exit interrupts
-- its children. The helper is interrupted before it resolves the hint: the wake is lost, the
-- taker waits for good, and the root has no exit.
#guard verdict (signallerExits (opsOf { post := postWith ⟨false, false, .interruptible⟩ })) =
  "built"
#guard (exitOf
  (signallerExits (opsOf { post := postWith ⟨false, false, .interruptible⟩ }))).isNone
#guard (rowsOf
  (signallerExits (opsOf { post := postWith ⟨false, false, .interruptible⟩ }))).contains
    (.exited 3 false)

/-! ## 7. The receiver's continuation that grows

The helper's task runs the receiver: its next attempt, and then its caller's continuation, under
the task's own budget (decisions rows 226 and 238). Here the taker's continuation is a loop of
`n` steps. The measure is the least fuel at which the flush of the helper's task ends the root.
The count of signals is one at every length, and the queue's state is the same.

**No bound is claimed.** The numbers are measured on this program at these lengths. -/

/-- A taker whose continuation runs `n` steps; the root offers, and joins it. -/
def grows (n : Nat) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let count ← Ref.make (nat 0)
  let f ← fork (eff do
    let x ← Queue.take .nat q
    let _ ← forRange (nat 0) (nat n) fun _ => Ref.updateWith count fun c => app "succ" [c]
    return x)
  let _ ← Queue.offer .nat q (nat 7)
  let x ← join f
  let c ← Ref.get count
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

-- Each program builds, and it answers its message and its count of steps.
#guard measured.all fun (n, _) =>
  exitOf (grows n) == some (.success (.list [.nat 7, .nat n]))
-- At the measured fuel the flush ends the root. The empty continuation is the control: 49.
#guard measured.all fun (n, least) => afterFlush (grows n) least == some (true, true)
-- At one less it does not. And five more flushes at the ample fuel do not end it either: the
-- cut inside the dispatch lost the work that remained, and a later flush is no resumption.
-- Decisions row 226 excludes that cut from the first profile, so this is the excluded case,
-- and no fault of the wrapper.
#guard measured.all fun (n, least) => afterFlush (grows n) (least - 1) == some (false, false)
-- The measured fuel grows with the continuation: three for each step, at these lengths.
#guard measured.all fun (n, least) => least == 49 + 3 * n

end Test.Program.QueueTraces
