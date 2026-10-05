import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops

/-!
# Probe: the Queue's operations as programs of the tree, before the fold and the mask

Status: research evidence (2026-10-05, base `c09826c0`). A finite probe: one schedule for each
scenario, on the Lean machine only. `QueueSkeleton.out` beside this file is its output.

    lake env lean docs/research/2026-10-05-claude-lead/queue-readiness/QueueSkeleton.lean

What it stands in for. The cell keeps two lists and two indexes, because the tree has no list
fold, no `take`, no `drop` and no identity test before seat FOLD merges. `uninterruptible` stands
for the mask and `interruptible` for its restore, which is right under an interruptible caller
only. A taker waits once and keeps one hint: the probe does not renew a hint.

What it shows. `take` and `offer` build and run with the constructs of today: one `Ref.modify`
with a binder term over a record that holds a list of `Deferred` handles; the posted helper of
decisions row 238; a wait and a second attempt; strict order with two takers; a withdrawal when
the wait is interrupted. The cleanup is the pin's `onInterrupt`: `onExit` with
`causeIsInterrupt` on the exit, which keeps the interruptor. A `catchCause` that fails again
with `Cause.interrupt none` loses it (S5 against its control).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace QueueSkeleton
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- A hint: a Deferred that carries nothing and cannot fail. -/
def hintTy : Ty := .deferredOf .unit .never

def stateFields : List (String × Bool × Ty) :=
  [("msgs", false, .list .nat), ("mHead", false, .nat),
   ("takers", false, .list hintTy), ("tHead", false, .nat), ("withdrawn", false, .nat)]

def state0 : TermSrc :=
  record stateFields [("msgs", app "nil" []), ("mHead", nat 0), ("takers", app "nil" []),
    ("tHead", nat 0), ("withdrawn", nat 0)]

def len (xs : TermSrc) : TermSrc := app "length" [xs]
def snoc (xs x : TermSrc) : TermSrc := app "append" [xs, app "cons" [x, app "nil" []]]
def ready (s : TermSrc) : TermSrc := app "lt" [field s "mHead", len (field s "msgs")]
def waiting (s : TermSrc) : TermSrc := app "lt" [field s "tHead", len (field s "takers")]

/-- The hint to signal: the earliest waiting taker's, when a message is ready. -/
def wake (s : TermSrc) : TermSrc :=
  app "ite" [ready s, app "get" [field s "takers", field s "tHead"], app "none" []]

/-- An offer into an unbounded buffer. Answer: the signal. -/
def offerStep (a s : TermSrc) : TermSrc :=
  let s' := recordSet s "msgs" (snoc (field s "msgs") a)
  app "pair" [wake s', s']

/-- A taker's first attempt. Answer: `[message?, position, signal?]`. -/
def tryTake (hint s : TermSrc) : TermSrc :=
  let consumed := recordSet s "mHead" (app "succ" [field s "mHead"])
  let enrolled := recordSet s "takers" (snoc (field s "takers") hint)
  app "ite" [app "and" [ready s, app "not" [waiting s]],
    app "pair" [tuple [app "get" [field s "msgs", field s "mHead"], nat 0, wake consumed], consumed],
    app "pair" [tuple [app "none" [], len (field s "takers"), app "none" []], enrolled]]

/-- A waiting taker's later attempt, at its position. Answer: `[message?, signal?]`. -/
def retryTake (p s : TermSrc) : TermSrc :=
  let consumed := recordSet (recordSet s "mHead" (app "succ" [field s "mHead"]))
    "tHead" (app "succ" [field s "tHead"])
  app "ite" [app "and" [ready s, app "eq" [field s "tHead", p]],
    app "pair" [tuple [app "get" [field s "msgs", field s "mHead"], wake consumed], consumed],
    app "pair" [tuple [app "none" [], app "none" []], s]]

/-- The earliest taker leaves. Answer: the signal that passes on. -/
def withdraw (p s : TermSrc) : TermSrc :=
  let counted := recordSet s "withdrawn" (app "succ" [field s "withdrawn"])
  let left := recordSet counted "tHead" (app "succ" [field s "tHead"])
  app "ite" [app "eq" [field s "tHead", p],
    app "pair" [wake left, left],
    app "pair" [app "none" [], counted]]

/-- Row 238: a detached fork with a deferred start, uninterruptible. -/
def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- Post one signal: the helper resolves the hint. -/
def post (signal : TermSrc) : Src NativeOp :=
  selectOption "h" signal (succeed unit)
    (andThen (withFiber (Action.fork (Deferred.succeed (var "h") unit) posted)) (succeed unit))

def offer (q a : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let signal ← Ref.modify "s" (offerStep a (var "s")) q
    let _ ← post signal
    return bool true)

/-- `take` under an interruptible caller: `uninterruptible` stands for the mask, and
`interruptible` for its restore. The cleanup re-raises an interrupt with no interruptor. -/
def take (q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let hint ← Deferred.make .unit .never
    let r ← Ref.modify "s" (tryTake hint (var "s")) q
    let _ ← post (tupleAt r 2)
    selectOption "m" (tupleAt r 0)
      (eff do
        let _ ← catchCause "c" (interruptible (Deferred.await hint))
          (eff do
            let signal ← Ref.modify "s" (withdraw (tupleAt r 1) (var "s")) q
            let _ ← post signal
            failCause (Cause.interrupt none))
        let r2 ← Ref.modify "s" (retryTake (tupleAt r 1) (var "s")) q
        let _ ← post (tupleAt r2 1)
        selectOption "m2" (tupleAt r2 0) (fail (str "woken without a message"))
          (succeed (var "m2")))
      (succeed (var "m")))

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

def showReason : Reason Err Defect FiberId Ann → String
  | .fail _ _ => "fail"
  | .interrupt who _ => "interrupt by " ++ toString (repr who)
  | .die _ _ => "die"

def showExit : Option ExitV → String
  | none => "no exit"
  | some (.success v) => "success " ++ toString (repr v)
  | some (.failure c) => "failure " ++ toString (c.reasons.map showReason)

def exitOf (src : Src NativeOp) (flushes : Nat := 1) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => "not built"
  | .ok b =>
    let r := (List.range flushes).foldl (fun (s : Run) _ => s.control Effect4.Api.flush)
      (Run.runPure b "q" { fuel := 4000, compileFuel := 4000 })
    showExit r.exit

/-- S1: two offers, then two takes. Nobody waits. -/
def s1 : Src NativeOp := eff do
  let q ← Ref.make state0
  let _ ← offer q (nat 1)
  let _ ← offer q (nat 2)
  let a ← take q
  let b ← take q
  return tuple [a, b]

/-- S2: a taker waits; an offer wakes it through the posted helper. -/
def s2 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (take q)
  let _ ← offer q (nat 7)
  let a ← join f
  return a

/-- S3: two takers wait in order; two offers; each gets its message in order. -/
def s3 : Src NativeOp := eff do
  let q ← Ref.make state0
  let fa ← fork (take q)
  let fb ← fork (take q)
  let _ ← offer q (nat 1)
  let _ ← offer q (nat 2)
  let a ← join fa
  let b ← join fb
  return tuple [a, b]

/-- S4: a waiting taker is interrupted; a later offer stays; the next take is not blocked. -/
def s4 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (take q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← offer q (nat 5)
  let a ← take q
  let s ← Ref.get q
  return tuple [a, field s "withdrawn", field s "tHead"]

/-- S5: the interrupted taker's own exit, reified. -/
def s5 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (take q)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return e

/-- Control of S5: a fiber parked on an interruptible wait with no cleanup. -/
def s5control : Src NativeOp := eff do
  let hint ← Deferred.make .unit .never
  let f ← fork (uninterruptible (interruptible (Deferred.await hint)))
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return e

#eval verdict (mk s1)
#eval verdict (mk s2)
#eval verdict (mk s3)
#eval verdict (mk s4)
#eval verdict (mk s5)
#eval verdict (mk s5control)

#eval (Effect4.Api.Author.build (mk s1)).toOption.map fun b => toString (repr (b.ty.answer, b.ty.error))

#eval exitOf s1
#eval exitOf s1 3
#eval exitOf s2
#eval exitOf s2 3
#eval exitOf s3
#eval exitOf s3 3
#eval exitOf s4
#eval exitOf s4 3
#eval exitOf s5
#eval exitOf s5 3
#eval exitOf s5control
#eval exitOf s5control 3

/-! ## The cleanup on interruption: three candidates -/

/-- S6. The handler cleans up and then enters an interruptible region. If the machine delivers
a pending interrupt there, the fiber fails with the first cause, interruptor included. -/
def s6 : Src NativeOp := eff do
  let n ← Ref.make (nat 0)
  let hint ← Deferred.make .unit .never
  let f ← fork (uninterruptible (eff do
    let _ ← catchCause "c" (interruptible (Deferred.await hint))
      (andThen (Ref.update "k" (app "succ" [var "k"]) n) (interruptible (succeed unit)))
    return nat 99))
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let k ← Ref.get n
  return tuple [e, k]

/-- S6b. The handler cleans up and succeeds. Does the interrupt come back when the mask ends? -/
def s6b : Src NativeOp := eff do
  let n ← Ref.make (nat 0)
  let hint ← Deferred.make .unit .never
  let f ← fork (uninterruptible (eff do
    let _ ← catchCause "c" (interruptible (Deferred.await hint))
      (Ref.update "k" (app "succ" [var "k"]) n)
    return nat 99))
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let k ← Ref.get n
  return tuple [e, k]

/-- S7. `onExit` with a finalizer that always runs: the exit stays the body's. -/
def s7 : Src NativeOp := eff do
  let n ← Ref.make (nat 0)
  let hint ← Deferred.make .unit .never
  let f ← fork (uninterruptible (eff do
    let _ ← onExit "e" (interruptible (Deferred.await hint))
      (Ref.update "k" (app "succ" [var "k"]) n)
    return nat 99))
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let k ← Ref.get n
  return tuple [e, k]

/-- S7b. The same finalizer on a wait that succeeds: it runs too, which a withdrawal must not. -/
def s7b : Src NativeOp := eff do
  let n ← Ref.make (nat 0)
  let hint ← Deferred.make .unit .never
  let f ← fork (uninterruptible (eff do
    let _ ← onExit "e" (interruptible (Deferred.await hint))
      (Ref.update "k" (app "succ" [var "k"]) n)
    return nat 99))
  let _ ← Deferred.succeed hint unit
  let e ← await f
  let k ← Ref.get n
  return tuple [e, k]

/-- S8. No atom reads an exit: `causeIsInterrupt` on the exit that `onExit` binds. -/
def s8 : Src NativeOp := eff do
  let hint ← Deferred.make .unit .never
  let _ ← onExit "e" (Deferred.await hint)
    (ifElse (app "causeIsInterrupt" [var "e"]) (succeed unit) (succeed unit))
  return nat 1

/-! ## The loop forms -/

/-- Post every hint of a list: a loop over an index. -/
def postAll (hints : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len hints]
      body := fun i => post (app "get" [hints, i])
      step := fun i _ => app "succ" [i] }

/-- The cleanup of a wait, as the pin defines `onInterrupt`: `onExit` with a test of the exit
(`onInterrupt`, `exitHasInterrupts`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`). -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- `take` as a loop that ends with the message: the cursor is the message, absent at first. -/
def takeLoop (q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let hint ← Deferred.make .unit .never
    let r ← Ref.modify "s" (tryTake hint (var "s")) q
    let _ ← post (tupleAt r 2)
    let got ← iterateWith (tupleAt r 0)
      { cursorTy := some (.option .nat)
        while_ := fun c => app "not" [app "isSome" [c]]
        body := fun _ => eff do
          let _ ← onInterrupt (interruptible (Deferred.await hint))
            (eff do
              let signal ← Ref.modify "s" (withdraw (tupleAt r 1) (var "s")) q
              post signal)
          let r2 ← Ref.modify "s" (retryTake (tupleAt r 1) (var "s")) q
          let _ ← post (tupleAt r2 1)
          return tupleAt r2 0
        step := fun _ a => a }
    selectOption "m" got (failCause (Cause.die (str "queue: the loop ended without a message")))
      (succeed (var "m")))

/-- S9: S3 with the loop form: two takers in order, two offers. -/
def s9 : Src NativeOp := eff do
  let q ← Ref.make state0
  let fa ← fork (takeLoop q)
  let fb ← fork (takeLoop q)
  let _ ← offer q (nat 1)
  let _ ← offer q (nat 2)
  let a ← join fa
  let b ← join fb
  return tuple [a, b]

/-- S10: the interrupted taker's own exit with the faithful cleanup, and the withdrawal count. -/
def s10 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (takeLoop q)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let s ← Ref.get q
  return tuple [e, field s "withdrawn"]

/-- S11: S4 with the loop form: after the withdrawal a later offer stays and a take gets it. -/
def s11 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (takeLoop q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← offer q (nat 5)
  let a ← takeLoop q
  let s ← Ref.get q
  return tuple [a, field s "withdrawn", field s "tHead"]

/-- S12: the cleanup does not run when the wait succeeds: one taker, one offer, no withdrawal. -/
def s12 : Src NativeOp := eff do
  let q ← Ref.make state0
  let f ← fork (takeLoop q)
  let _ ← offer q (nat 3)
  let a ← join f
  let s ← Ref.get q
  return tuple [a, field s "withdrawn"]

/-- S13: every hint of a list is posted: two parked fibers, one list, both resume. -/
def s13 : Src NativeOp := eff do
  let h1 ← Deferred.make .unit .never
  let h2 ← Deferred.make .unit .never
  let f1 ← fork (andThen (Deferred.await h1) (succeed (nat 1)))
  let f2 ← fork (andThen (Deferred.await h2) (succeed (nat 2)))
  let _ ← postAll (app "cons" [h1, app "cons" [h2, app "nil" []]])
  let a ← join f1
  let b ← join f2
  return tuple [a, b]

#eval "--- candidates"
#eval (verdict (mk s6), verdict (mk s6b), verdict (mk s7), verdict (mk s7b), verdict (mk s8))
#eval exitOf s6 3
#eval exitOf s6b 3
#eval exitOf s7 3
#eval exitOf s7b 3
#eval "--- loops and the faithful cleanup"
#eval (verdict (mk s9), verdict (mk s10), verdict (mk s11), verdict (mk s12), verdict (mk s13))
#eval (Effect4.Api.Author.build (mk s9)).toOption.map fun b => toString (repr (b.ty.answer, b.ty.error))
#eval exitOf s9 3
#eval exitOf s10 3
#eval exitOf s11 3
#eval exitOf s12 3
#eval exitOf s13 3

end QueueSkeleton
