import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Profile

/-!
# The Queue's steps on the machine: the probe's eight scenarios (decisions row 255)

Each scenario is one program over the library's step terms
(`src/Effect4/Modules/Queue/Steps.lean`), run on the Lean machine: one schedule, with three
flushes of the posted helpers. The answers are the probe's
(`docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean` and its output beside
it).

**The operations here are the probe's, and they are test fixtures.** `take`, `offer` and `size`
wrap the steps with a wait, a posted helper for each notification (decisions rows 238 and 240)
and a withdrawal on interruption. `uninterruptible` stands for the mask and `interruptible` for
its restore, which is right under an interruptible caller only. The public operations come with
the wrapper's slice, after the mask (decisions row 251).

Placement. Each scenario is a finite control of the proposed claim `queue-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the steps' use in a
program. Every guard is one run. None proves delivery, a cancellation law or liveness, and none
is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The operations, as the probe writes them

Each operation writes its step's row with a fixed name for the cell's current value:
`Ref.modify "s" (step … (var "s")) q`. A row elaborates its whole term under that binder, so a
caller's term that read a variable named `s` would read the cell's value instead. Here every
other term under the binder is closed or is this battery's own: the identity and the hint that
the operation binds itself, and a message that each scenario writes as a literal. The module
exports no row: each step takes the current value's source (addendum 2 of the seat's brief).
The public wrapper will mint the name. -/

/-- Decisions row 238: a detached fork with a deferred start, uninterruptible. -/
def posted : Effect4.Supervision.ForkOptions := ⟨false, true, .uninterruptible⟩

/-- Post one helper for each request of a list: it resolves the request's hint with one answer
(decisions rows 238 and 240). -/
def postAll (requests answer : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOption "r" (app "get" [requests, i]) (succeed unit)
        (andThen
          (withFiber (Action.fork (Deferred.succeed (field (var "r") "hint") answer) posted))
          (succeed unit))
      step := fun i _ => app "succ" [i] }

/-- The pin's `onInterrupt`: `onExit` with a test of the exit. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- `take`. A step's notifications are posted in the model's order: the accepted offers'
answers, then the taker's wake. -/
def take (A : Ty) (q : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let got ← iterateWith noneT
      { cursorTy := some (.option A)
        while_ := fun c => notT (app "isSome" [c])
        body := fun _ => eff do
          let hint ← Deferred.make .unit .never
          let r ← Ref.modify "s" (Queue.takeStep A id hint (var "s")) q
          let _ ← postAll (tupleAt r 1) (bool true)
          let _ ← postAll (tupleAt r 2) unit
          selectOption "m" (tupleAt r 0)
            (andThen
              (onInterrupt (interruptible (Deferred.await hint))
                (eff do
                  let woken ← Ref.modify "s" (Queue.withdrawTake A id (var "s")) q
                  postAll woken unit))
              (succeed noneT))
            (succeed (app "some" [var "m"]))
        step := fun _ a => a }
    selectOption "m" got (failCause (Cause.die (str "queue: the loop ended without a message")))
      (succeed (var "m")))

def offer (A : Ty) (q a : TermSrc) : Src NativeOp :=
  uninterruptible (eff do
    let id ← Deferred.make .unit .never
    let hint ← Deferred.make .bool .never
    let r ← Ref.modify "s" (Queue.offerStep A id hint a (var "s")) q
    let _ ← postAll (tupleAt r 1) unit
    selectOption "ok" (tupleAt r 0)
      (onInterrupt (interruptible (Deferred.await hint))
        (eff do
          let woken ← Ref.modify "s" (Queue.withdrawOffer A id (var "s")) q
          postAll woken unit))
      (succeed (var "ok")))

/-- `size`: a read of the cell, and the size step over the value. -/
def size (A : Ty) (q : TermSrc) : Src NativeOp := eff do
  let s ← Ref.get q
  return Queue.sizeStep A s

/-! ## Runs -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

/-- The root exit of a source's run, after three flushes of the posted helpers. -/
def exitOf (src : Src NativeOp) : Option ExitV :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => none
  | .ok b =>
    ((List.range 3).foldl (fun (s : Run) _ => s.control Effect4.Api.flush)
      (Run.runPure b "q" { fuel := 20000, compileFuel := 20000 })).exit

/-- The answer and error types of a built source. -/
def typesOf (src : Src NativeOp) : Option (Ty × Ty) :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => (b.ty.answer, b.ty.error)

/-! ## The eight scenarios, at number messages -/

/-- R1: two offers into room, then two takes. -/
def r1 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let a ← offer .nat q (nat 1)
  let b ← offer .nat q (nat 2)
  let x ← take .nat q
  let y ← take .nat q
  return tuple [a, b, x, y]

/-- R2: a taker waits; an offer wakes it. -/
def r2 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let f ← fork (take .nat q)
  let _ ← offer .nat q (nat 7)
  let x ← join f
  return x

/-- R3: two takers wait in order; two offers; each gets its message in order. -/
def r3 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let fa ← fork (take .nat q)
  let fb ← fork (take .nat q)
  let _ ← offer .nat q (nat 1)
  let _ ← offer .nat q (nat 2)
  let x ← join fa
  let y ← join fb
  return tuple [x, y]

/-- R4: capacity one. A second offer waits; the take that frees room accepts it and its answer
is posted; then the second message is taken. -/
def r4 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 1)
  let a ← offer .nat q (nat 1)
  let f ← fork (offer .nat q (nat 2))
  let x ← take .nat q
  let b ← join f
  let y ← take .nat q
  return tuple [a, x, b, y]

/-- R5: a waiting taker is interrupted; a later offer stays; the next take gets it. -/
def r5 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let f ← fork (take .nat q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← offer .nat q (nat 5)
  let x ← take .nat q
  let s ← Ref.get q
  return tuple [x, len (field s "takers")]

/-- R6: capacity one. A pending offer is interrupted before any step accepts it: its message
never enters. -/
def r6 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 1)
  let _ ← offer .nat q (nat 1)
  let f ← fork (offer .nat q (nat 2))
  let _ ← withFiber (Action.interrupt f)
  let x ← take .nat q
  let n ← size .nat q
  let s ← Ref.get q
  return tuple [x, n, len (field s "offers")]

/-- R7: the interrupted taker's own exit keeps its interruptor. -/
def r7 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let f ← fork (take .nat q)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return e

/-- R8: the order of a step's notifications (Codex's control). Capacity one; takers A and B
wait; message 1 is offered; a second offer waits at the full buffer. A's take frees room: it
accepts the second offer and leaves B ready. The model names the offerer first and B second.
Each fiber writes its mark when it goes on, so the log shows the order of the two resumptions:
A's own mark, then the offerer's `101`, then B's message. -/
def r8 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 1)
  let log ← Ref.make (app "take" [app "cons" [nat 0, nilT], nat 0])
  let fa ← fork (eff do
    let x ← take .nat q
    Ref.update "l" (snoc (var "l") x) log)
  let fb ← fork (eff do
    let x ← take .nat q
    Ref.update "l" (snoc (var "l") x) log)
  let _ ← offer .nat q (nat 1)
  let fc ← fork (eff do
    let _ ← offer .nat q (nat 2)
    Ref.update "l" (snoc (var "l") (nat 101)) log)
  let _ ← join fa
  let _ ← join fb
  let _ ← join fc
  let l ← Ref.get log
  return l

-- Each scenario builds: the checker types every step inside its `Ref.modify`.
#guard [r1, r2, r3, r4, r5, r6, r7, r8].map verdict = List.replicate 8 "built"
-- R4's types: the two offers' answers and the two messages, and no failure.
#guard typesOf r4 = some (.tuple [.bool, .nat, .bool, .nat], .never)

-- The machine's answers, as the probe recorded them.
#guard exitOf r1 = some (.success (.list [.bool true, .bool true, .nat 1, .nat 2]))
#guard exitOf r2 = some (.success (.nat 7))
#guard exitOf r3 = some (.success (.list [.nat 1, .nat 2]))
#guard exitOf r4 = some (.success (.list [.bool true, .nat 1, .bool true, .nat 2]))
#guard exitOf r5 = some (.success (.list [.nat 5, .nat 0]))
#guard exitOf r6 = some (.success (.list [.nat 1, .nat 0, .nat 0]))
-- R7: the reified exit of the interrupted taker: a failure with one interruption, by fiber 0.
#guard exitOf r7 = some (.success (.ctor 1 [.ctor 0 [.list [.ctor 2 [.some (.ctor 0 [.nat 0]),
  .ctor 0 [.list [.pair (.str "stack1") .unit, .pair (.str "stack0") .unit]]]]]]))
-- R8: A's mark, then the offerer's, then B's message.
#guard exitOf r8 = some (.success (.list [.nat 1, .nat 101, .nat 2]))

-- Red control of the pins: R8's log in the first draft's order, the wake before the answer.
#guard exitOf r8 != some (.success (.list [.nat 1, .nat 2, .nat 101]))

/-! ## The same operations on the abstract model -/

open Effect4.Queue.Model in
/-- R1 on the model: both offers accepted, then the two messages in order. -/
def model1 : OfferReply × OfferReply × TakeReply × TakeReply :=
  let s : State := { capacity := some 2 }
  let a := Queue.Model.offer s 100 1
  let b := Queue.Model.offer a.1 101 2
  let x := Queue.Model.take b.1 ⟨1, 1, 1⟩
  let y := Queue.Model.take x.1 ⟨2, 1, 1⟩
  (a.2.1, b.2.1, x.2.1, y.2.1)

open Effect4.Queue.Model in
/-- R4 on the model: the second offer waits; the take frees room and answers it; then the
second message. -/
def model4 : OfferReply × OfferReply × TakeReply × List Signal × TakeReply :=
  let s : State := { capacity := some 1 }
  let a := Queue.Model.offer s 100 1
  let b := Queue.Model.offer a.1 101 2
  let x := Queue.Model.take b.1 ⟨1, 1, 1⟩
  let y := Queue.Model.take x.1 ⟨2, 1, 1⟩
  (a.2.1, b.2.1, x.2.1, x.2.2, y.2.1)

#guard model1 = (.accepted true, .accepted true, .got [1], .got [2])
#guard model4 = (.accepted true, .wait, .got [1], [⟨101, .offered true⟩], .got [2])

/-! ## At another message type

The same two scenarios at string messages: the module's builders take the message type, and
the checker types each step in a cell of strings. -/

/-- R1 at strings. -/
def r1Strings : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .string 2)
  let a ← offer .string q (str "a")
  let b ← offer .string q (str "b")
  let x ← take .string q
  let y ← take .string q
  return tuple [a, b, x, y]

/-- R4 at strings. -/
def r4Strings : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .string 1)
  let a ← offer .string q (str "a")
  let f ← fork (offer .string q (str "b"))
  let x ← take .string q
  let b ← join f
  let y ← take .string q
  return tuple [a, x, b, y]

#guard [r1Strings, r4Strings].map verdict = ["built", "built"]
#guard exitOf r1Strings =
  some (.success (.list [.bool true, .bool true, .str "a", .str "b"]))
#guard exitOf r4Strings =
  some (.success (.list [.bool true, .str "a", .bool true, .str "b"]))
-- Red control of the message type: a number offered into a cell of strings does not build.
#guard verdict (eff do
  let q ← Ref.make (Queue.empty .string 2)
  let a ← offer .string q (nat 1)
  return a) != "built"

end Test.Program.QueueScenarios
