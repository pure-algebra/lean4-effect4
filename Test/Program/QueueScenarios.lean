import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Library.Queue.Ops
import Effect4.Laws.Library.Queue.Profile

/-!
# The Queue's operations on the machine: the probe's eight scenarios (rows 233 and 255)

Each scenario is one program over the library's operations
(`src/Effect4/Library/Queue/Ops.lean`), run on the Lean machine on one schedule. The answers are
the probe's (`docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean` and its
output beside it).

**The operations are the library's.** `Queue.bounded`, `Queue.offer`, `Queue.take` and
`Queue.size` wrap the step terms with the shared waiting wrapper
(`src/Effect4/Library/Waiting.lean`): the mask that restores, a posted helper for each
notification, and a withdrawal on interruption. Every binder of an operation is minted.

**The fixtures of the earlier slices stay here as written forms** (the namespace `Written`).
Each writes its binders by name, and each takes its mask as an argument:

- `restoring` is the mask that restores. With it a written form is the library's operation, tree
  for tree: each scenario's program has the same canonical bytes over either.
- `standIn` is the earlier fixture: `uninterruptible` for the mask and `interruptible` for its
  restore. It is right under an interruptible caller only. Its programs are other trees, and
  they give the same answers on these eight scenarios, where no caller is masked.

The written forms are the red controls of the hygiene controls (`Test/Program/QueueOps.lean`):
a caller's variable of a written name reads the operation's own binder there.

Placement. Each scenario is a finite control of the proposed claim `queue-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the operations' use in a
program. Every guard is one run. None proves delivery, a cancellation law or liveness, and none
is a host run: the host runs are the truth lane's (`harness/truth/Truth.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The operations of a scenario -/

/-- The operations that a scenario runs. The library's are `library`. A written form is one more
value, for the byte comparison and for the red controls. -/
structure Ops where
  take : Ty → TermSrc → Src NativeOp
  offer : Ty → TermSrc → TermSrc → Src NativeOp
  size : Ty → TermSrc → Src NativeOp

/-- The library's operations. -/
def library : Ops := { take := Queue.take, offer := Queue.offer, size := Queue.size }

/-! ## The written forms: the fixtures of the earlier slices

Each operation writes its step's row with a fixed name for the cell's current value:
`Ref.modify "s" (step … (var "s")) q`. A row elaborates its whole term under that binder. So a
caller's variable named `s` would read the cell's value there, and the same holds of `id`,
`hint`, `r` and `e` at their binders. -/

namespace Written

/-- How a written form masks: it hands its body the restore of the mask. -/
abbrev Mask := ((Src NativeOp → Src NativeOp) → Src NativeOp) → Src NativeOp

/-- The mask that restores (decisions rows 244 to 246). -/
def restoring : Mask := uninterruptibleMaskWith

/-- The two stand-ins of the earlier fixture: `uninterruptible` for the mask and
`interruptible` for its restore, whatever the caller. -/
def standIn : Mask := fun body => uninterruptible (body interruptible)

/-- Post one helper for each request of a list, with the request under the written name `r`. -/
def postAll (requests answer : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len requests]
      body := fun i => selectOption "r" (app "get" [requests, i]) (succeed unit)
        (andThen
          (withFiber (Action.fork (Deferred.succeed (field (var "r") "hint") answer) posted))
          (succeed unit))
      step := fun i _ => app "succ" [i] }

/-- The pin's `onInterrupt`, with the exit under the written name `e`. -/
def onInterrupt (body cleanup : Src NativeOp) : Src NativeOp :=
  onExit "e" body (ifElse (app "causeIsInterrupt" [var "e"]) cleanup (succeed unit))

/-- `take`, as the fixture writes it, under a mask. -/
def take (mask : Mask) (A : Ty) (q : TermSrc) : Src NativeOp :=
  mask fun restore => eff do
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
              (onInterrupt (restore (Deferred.await hint))
                (eff do
                  let woken ← Ref.modify "s" (Queue.withdrawTake A id (var "s")) q
                  postAll woken unit))
              (succeed noneT))
            (succeed (app "some" [var "m"]))
        step := fun _ a => a }
    selectOption "m" got (failCause (Cause.die (str "queue: the loop ended without a message")))
      (succeed (var "m"))

/-- `offer`, as the fixture writes it, under a mask. -/
def offer (mask : Mask) (A : Ty) (q a : TermSrc) : Src NativeOp :=
  mask fun restore => eff do
    let id ← Deferred.make .unit .never
    let hint ← Deferred.make .bool .never
    let r ← Ref.modify "s" (Queue.offerStep A id hint a (var "s")) q
    let _ ← postAll (tupleAt r 1) unit
    selectOption "ok" (tupleAt r 0)
      (onInterrupt (restore (Deferred.await hint))
        (eff do
          let woken ← Ref.modify "s" (Queue.withdrawOffer A id (var "s")) q
          postAll woken unit))
      (succeed (var "ok"))

/-- `size`, as the fixture writes it. -/
def size (A : Ty) (q : TermSrc) : Src NativeOp := eff do
  let s ← Ref.get q
  return Queue.sizeStep A s

/-- The written forms under a mask, as the operations of a scenario. -/
def ops (mask : Mask) : Ops := { take := take mask, offer := offer mask, size := size }

end Written

/-! ## Runs -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

/-- The fuel of each run here, and of the engine's fixture. -/
def fuel : Nat := 20000

/-- The root exit of a source's run, after three more flushes of the posted helpers. -/
def exitOf (src : Src NativeOp) : Option ExitV :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => none
  | .ok b =>
    ((List.range 3).foldl (fun (s : Run) _ => s.control Effect4.Api.flush)
      (Run.runPure b "q" { fuel := fuel, compileFuel := fuel })).exit

/-- The root exit of the ordinary run at a fuel: the root evaluated, then one flush. The truth
lane runs each program so, at the fuel 1000. -/
def exitAt (budget : Nat) (src : Src NativeOp) : Option ExitV :=
  ((Effect4.Api.Author.build (mk src)).toOption.bind fun b => (Api.run b.program budget).exit)

/-- The answer and error types of a built source. -/
def typesOf (src : Src NativeOp) : Option (Ty × Ty) :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => (b.ty.answer, b.ty.error)

/-- The canonical bytes of a source's built program. -/
def bytesOf (src : Src NativeOp) : Option Store.Bytes :=
  (Effect4.Api.Author.build (mk src)).toOption.map fun b => Api.bytesOf b.program

/-! ## The eight scenarios, at number messages -/

/-- R1: two offers into room, then two takes. -/
def r1With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let a ← ops.offer .nat q (nat 1)
  let b ← ops.offer .nat q (nat 2)
  let x ← ops.take .nat q
  let y ← ops.take .nat q
  return tuple [a, b, x, y]

/-- R2: a taker waits; an offer wakes it. -/
def r2With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (ops.take .nat q)
  let _ ← ops.offer .nat q (nat 7)
  let x ← join f
  return x

/-- R3: two takers wait in order; two offers; each gets its message in order. -/
def r3With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let fa ← fork (ops.take .nat q)
  let fb ← fork (ops.take .nat q)
  let _ ← ops.offer .nat q (nat 1)
  let _ ← ops.offer .nat q (nat 2)
  let x ← join fa
  let y ← join fb
  return tuple [x, y]

/-- R4: capacity one. A second offer waits; the take that frees room accepts it and its answer
is posted; then the second message is taken. -/
def r4With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let a ← ops.offer .nat q (nat 1)
  let f ← fork (ops.offer .nat q (nat 2))
  let x ← ops.take .nat q
  let b ← join f
  let y ← ops.take .nat q
  return tuple [a, x, b, y]

/-- R5: a waiting taker is interrupted; a later offer stays; the next take gets it. -/
def r5With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (ops.take .nat q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← ops.offer .nat q (nat 5)
  let x ← ops.take .nat q
  let s ← Ref.get q
  return tuple [x, len (field s "takers")]

/-- R6: capacity one. A pending offer is interrupted before any step accepts it: its message
never enters. -/
def r6With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let _ ← ops.offer .nat q (nat 1)
  let f ← fork (ops.offer .nat q (nat 2))
  let _ ← withFiber (Action.interrupt f)
  let x ← ops.take .nat q
  let n ← ops.size .nat q
  let s ← Ref.get q
  return tuple [x, n, len (field s "offers")]

/-- R7: the interrupted taker's own exit keeps its interruptor. -/
def r7With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (ops.take .nat q)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return e

/-- R8: the order of a step's notifications (Codex's control). Capacity one; takers A and B
wait; message 1 is offered; a second offer waits at the full buffer. A's take frees room: it
accepts the second offer and leaves B ready. The model names the offerer first and B second.
Each fiber writes its mark when it goes on, so the log shows the order of the two resumptions:
A's own mark, then the offerer's `101`, then B's message. -/
def r8With (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let log ← Ref.make (app "take" [app "cons" [nat 0, nilT], nat 0])
  let fa ← fork (eff do
    let x ← ops.take .nat q
    Ref.update "l" (snoc (var "l") x) log)
  let fb ← fork (eff do
    let x ← ops.take .nat q
    Ref.update "l" (snoc (var "l") x) log)
  let _ ← ops.offer .nat q (nat 1)
  let fc ← fork (eff do
    let _ ← ops.offer .nat q (nat 2)
    Ref.update "l" (snoc (var "l") (nat 101)) log)
  let _ ← join fa
  let _ ← join fb
  let _ ← join fc
  let l ← Ref.get log
  return l

/-- The eight scenarios over one set of operations, in order. -/
def scenariosWith (ops : Ops) : List (Src NativeOp) :=
  [r1With ops, r2With ops, r3With ops, r4With ops, r5With ops, r6With ops, r7With ops, r8With ops]

def r1 : Src NativeOp := r1With library
def r2 : Src NativeOp := r2With library
def r3 : Src NativeOp := r3With library
def r4 : Src NativeOp := r4With library
def r5 : Src NativeOp := r5With library
def r6 : Src NativeOp := r6With library
def r7 : Src NativeOp := r7With library
def r8 : Src NativeOp := r8With library

-- Each scenario builds: the checker types every step inside its `Ref.modify`, and the mask's
-- saved state at each restore site.
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

-- The ordinary run gives each answer too, at the truth lane's fuel: the root evaluated, then
-- one flush. So no scenario needs a flush of its own.
#guard (scenariosWith library).all fun src =>
  (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src
-- Red control of the fuel: at a fuel of 5 no scenario has an exit.
#guard (scenariosWith library).all fun src => (exitAt 5 src).isNone

/-! ## The trees are kept: the library's operations against the written forms

`Api.bytesOf` is the canonical bytes of a built program. A tree holds no name: a binder is a
level. So the library's operation and the written form under the mask that restores are one
tree, and each scenario's program has the same bytes over either. -/

-- Each scenario over the library's operations has the bytes of the same scenario over the
-- written forms, under the mask that restores.
#guard (scenariosWith library).map bytesOf ==
  (scenariosWith (Written.ops Written.restoring)).map bytesOf
#guard ((scenariosWith library).map bytesOf).all Option.isSome
-- The construction is one `Ref.make` of the initial value: the fixtures' tree.
#guard elaborate (Queue.bounded .nat 2) == elaborate (Ref.make (Queue.empty .nat 2) : Src NativeOp)
-- Red control of the comparison: the eight programs are eight byte strings.
#guard ((scenariosWith library).map bytesOf).eraseDups.length = 8
-- The earlier fixture, with its two stand-ins, is another tree in each scenario: the mask is the
-- one difference of the library's programs from it.
#guard (List.zip (scenariosWith library) (scenariosWith (Written.ops Written.standIn))).all
  fun pair => bytesOf pair.1 != bytesOf pair.2
-- Under these eight schedules no caller is masked, so the stand-ins give the same answers.
#guard (scenariosWith (Written.ops Written.standIn)).map exitOf ==
  (scenariosWith library).map exitOf

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

The same two scenarios at string messages: the operations take the message type, and the checker
types each step in a cell of strings. -/

/-- R1 at strings. -/
def r1Strings : Src NativeOp := eff do
  let q ← Queue.bounded .string 2
  let a ← Queue.offer .string q (str "a")
  let b ← Queue.offer .string q (str "b")
  let x ← Queue.take .string q
  let y ← Queue.take .string q
  return tuple [a, b, x, y]

/-- R4 at strings. -/
def r4Strings : Src NativeOp := eff do
  let q ← Queue.bounded .string 1
  let a ← Queue.offer .string q (str "a")
  let f ← fork (Queue.offer .string q (str "b"))
  let x ← Queue.take .string q
  let b ← join f
  let y ← Queue.take .string q
  return tuple [a, x, b, y]

#guard [r1Strings, r4Strings].map verdict = ["built", "built"]
#guard exitOf r1Strings =
  some (.success (.list [.bool true, .bool true, .str "a", .str "b"]))
#guard exitOf r4Strings =
  some (.success (.list [.bool true, .str "a", .bool true, .str "b"]))
-- Red control of the message type: a number offered into a cell of strings does not build.
#guard verdict (eff do
  let q ← Queue.bounded .string 2
  let a ← Queue.offer .string q (nat 1)
  return a) != "built"

end Test.Program.QueueScenarios
