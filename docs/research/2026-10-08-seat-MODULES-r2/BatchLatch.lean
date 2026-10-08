import Test.Program.SemaphoreScenarios
import Effect4.Program.Authoring.Defs

/-! Probe MODS-10: a Latch that coalesces its wakes as rc.112 does (finding F3).

rc.112's `Latch` (`class Latch` of `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`):
`scheduleUnsafe` moves the waiters into a pending batch and schedules one flush task, or appends
them to the batch already scheduled; `flushScheduled` resumes the whole batch; an interrupted
waiter leaves the waiters or the pending batch.

Here the cell holds the same: `pending` and `scheduled` beside `open` and `waiters`. A wake posts
one flush helper only when no flush is scheduled; the helper takes the batch and resolves every
hint in order. The question: does the review's batch client then answer as Effect's Latch does? -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Program.SemaphoreScenarios (mark noNumbers)

namespace BatchLatch

def waiterFields : List (String × Bool × Ty) := [("hint", false, idTy), ("id", false, idTy)]
def waiterTy : Ty := .record waiterFields
/-- The cell, its names in canonical order. -/
def cellFields : List (String × Bool × Ty) :=
  [("open", false, .bool), ("pending", false, .list waiterTy), ("scheduled", false, .bool),
    ("waiters", false, .list waiterTy)]

def make (isOpen : Bool) : Src NativeOp :=
  Ref.make (record cellFields [("open", bool isOpen), ("pending", nilT), ("scheduled", bool false),
    ("waiters", nilT)])

def awaitStep (id hint s : TermSrc) : TermSrc :=
  ifT (field s "open") (app "pair" [bool true, s])
    (app "pair" [bool false, recordSet s "waiters"
      (snoc (removeById (field s "waiters") id) (record waiterFields [("id", id), ("hint", hint)]))])

/-- An interrupted waiter leaves the waiters and the pending batch. -/
def withdrawStep (id s : TermSrc) : TermSrc :=
  app "pair" [unit, recordSet (recordSet s "waiters" (removeById (field s "waiters") id))
    "pending" (removeById (field s "pending") id)]

/-- The wake: the reply is (the answer, whether to post a flush). -/
def wakeStep (setOpen : Bool) (s : TermSrc) : TermSrc :=
  let opened (t : TermSrc) : TermSrc := if setOpen then recordSet t "open" (bool true) else t
  let ws := field s "waiters"
  ifT (field s "open") (app "pair" [tuple [bool false, bool false], s])
    (ifT (isEmpty ws) (app "pair" [tuple [bool true, bool false], opened s])
      (ifT (field s "scheduled")
        (app "pair" [tuple [bool true, bool false], opened (recordSet
          (recordSet s "pending" (app "append" [field s "pending", ws])) "waiters" (noneOf ws))])
        (app "pair" [tuple [bool true, bool true], opened (recordSet (recordSet
          (recordSet s "pending" ws) "scheduled" (bool true)) "waiters" (noneOf ws))])))

/-- The flush takes the batch and clears the schedule. -/
def flushStep (s : TermSrc) : TermSrc :=
  app "pair" [field s "pending",
    recordSet (recordSet s "pending" (noneOf (field s "pending"))) "scheduled" (bool false)]

/-- Resolve every hint of a batch, in order, in this fiber. -/
def resolveAll (requests : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOptionWith (app "get" [requests, i]) (succeed unit) fun request =>
        andThen (Deferred.succeed (field request "hint") unit) (succeed unit)
      step := fun i _ => app "succ" [i] }

def flush (q : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith q flushStep) fun batch => resolveAll batch

def await (q : TermSrc) : Src NativeOp :=
  waitAnswer
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (awaitStep id hint)) fun passed => ifElse passed (done unit) wait
      withdraw := fun id => Ref.modifyWith q (withdrawStep id) }

def wake (setOpen : Bool) (q : TermSrc) : Src NativeOp :=
  uninterruptible
    (bindWith (Ref.modifyWith q (wakeStep setOpen)) fun reply =>
      andThen
        (ifElse (tupleAt reply 1) (andThen (withFiber (Action.fork (flush q) posted)) (succeed unit))
          (succeed unit))
        (succeed (tupleAt reply 0)))

structure Ops where
  make : Bool → Src NativeOp
  await : TermSrc → Src NativeOp
  openL : TermSrc → Src NativeOp
  release : TermSrc → Src NativeOp

def batched : Ops := { make, await, openL := wake true, release := wake false }

/-- The review's batch client (`LatchControls.batchClient`), over an operation record. -/
def batchClient (o : Ops) : Src NativeOp := eff do
  let l ← o.make false
  let log ← Ref.make noNumbers
  let a ← fork (andThen (o.await l) (mark log (nat 1)))
  let _ ← o.release l
  let middle ← withFiber (Action.fork (mark log (nat 9)) posted)
  let b ← fork (andThen (o.await l) (mark log (nat 2)))
  let _ ← o.release l
  let _ ← join a
  let _ ← join b
  let _ ← join middle
  Ref.get log

/-- MODS-4's d1 and d3, to check that the batch keeps their answers. -/
def d1 (o : Ops) : Src NativeOp := eff do
  let l ← o.make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (o.await l) (mark log (nat 1)))
  let _ ← o.release l
  let fb ← fork (andThen (o.await l) (mark log (nat 2)))
  let _ ← mark log (nat 3)
  let _ ← o.openL l
  let _ ← join fa
  let _ ← join fb
  Ref.get log

def d3 (o : Ops) : Src NativeOp := eff do
  let l ← o.make false
  let log ← Ref.make noNumbers
  let fa ← fork (andThen (o.await l) (mark log (nat 1)))
  let _ ← yieldNow 0
  let _ ← withFiber (Action.interrupt fa)
  let x ← o.openL l
  let _ ← mark log (nat 3)
  let y ← Ref.get log
  return tuple [x, y]

def exitOf (src : Src NativeOp) : Option ExitV :=
  match Api.Author.build { main := src } with
  | .ok b => (Api.run b.program 2000).exit
  | .error _ => none

end BatchLatch

open BatchLatch in
#eval [("batch", exitOf (batchClient batched)), ("d1", exitOf (d1 batched)),
  ("d3", exitOf (d3 batched))].map fun (n, e) => (n, e.isSome,
    match e with
    | some (.success v) => toString (repr v)
    | some (.failure _) => "failure"
    | none => "no exit")

-- The batch client over the coalescing Latch, admitted and printed for the native runner.
open BatchLatch in
#eval do
  match Api.Author.build { main := batchClient batched } with
  | .error _ => throw (IO.userError "batch client: Author.build refused")
  | .ok b =>
    match Api.printModule "main" b.program b.table with
    | none => throw (IO.userError "batch client: printModule refused")
    | some m =>
      IO.FS.writeFile "docs/research/2026-10-08-seat-MODULES-r2/batch-coalesced-lib.body.ts"
        (String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0)))
      IO.println "batch client over the coalescing Latch: admitted and printed"
