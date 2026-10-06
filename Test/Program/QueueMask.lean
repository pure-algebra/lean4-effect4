import Test.Program.QueueScenarios
import Effect4.Program.Authoring.Mask

/-!
# The Queue's `take` under the mask that restores (decisions rows 244 to 246, 251)

`Test/Program/QueueScenarios.lean` wraps the Queue's steps with two stand-ins:
`uninterruptible` for the mask and `interruptible` for its restore. That is right under an
interruptible caller only (`docs/research/2026-10-05-claude-lead/queue-readiness/queue-readiness.md`,
F5). Under a masked caller the restore must be the identity.

Here `take` is that file's `take` with the mask and its restore site in place of the two
stand-ins, and nothing else changed. The scenarios R2, R5 and R7 keep their answers. One
scenario is added: a taker under a masked caller is not interrupted while it waits.

The operation is a test fixture, as that file's are. The public wrapper comes with the
Queue's slice (decisions row 251). `offer` and `size` are that file's, unchanged.

Placement. Each scenario is a finite control of the claim `saved-mask-restoration` (concept
`scope-lifetime-finalization`, requirement R11) on the side of one client, and of the proposed
claim `waiting-request-obligation-preserved` (concept `reactive-scheduling`): an interruption
that is only requested, and stays pending under a mask, withdraws nothing. Every guard is one
run on one schedule. None proves delivery or liveness, none is a host run, and the mask's laws
name no declaration of the Queue.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueMask

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios (postAll onInterrupt offer size verdict exitOf typesOf)

/-- `take`, under the mask. The registration and the service pass run masked; the wait runs at
the caller's interruptibility, by the mask's own restore; the withdrawal on interruption runs
masked again. -/
def take (A : Ty) (q : TermSrc) : Src NativeOp :=
  uninterruptibleMaskWith fun restore => eff do
    let id ← Deferred.make .unit .never
    let got ← iterateWith Queue.noneT
      { cursorTy := some (.option A)
        while_ := fun c => Queue.notT (app "isSome" [c])
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
              (succeed Queue.noneT))
            (succeed (app "some" [var "m"]))
        step := fun _ a => a }
    selectOption "m" got (failCause (Cause.die (str "queue: the loop ended without a message")))
      (succeed (var "m"))

/-! ## R2, R5 and R7, with the masked `take` -/

/-- R2: a taker waits; an offer wakes it. -/
def r2 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let f ← fork (take .nat q)
  let _ ← offer .nat q (nat 7)
  let x ← join f
  return x

/-- R5: a waiting taker is interrupted; a later offer stays; the next take gets it. -/
def r5 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let f ← fork (take .nat q)
  let _ ← withFiber (Action.interrupt f)
  let _ ← offer .nat q (nat 5)
  let x ← take .nat q
  let s ← Ref.get q
  return tuple [x, Queue.len (field s "takers")]

/-- R7: the interrupted taker's own exit keeps its interruptor. -/
def r7 : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let f ← fork (take .nat q)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return e

-- Each scenario builds: the checker types the saved state and its restore site inside the
-- loop's body, and the answer and error types are the stand-in version's.
#guard [r2, r5, r7].map verdict = List.replicate 3 "built"
#guard typesOf r2 = typesOf Test.Program.QueueScenarios.r2
#guard typesOf r5 = typesOf Test.Program.QueueScenarios.r5

-- The three scenarios keep their answers.
#guard exitOf r2 = some (.success (.nat 7))
#guard exitOf r5 = some (.success (.list [.nat 5, .nat 0]))
#guard exitOf r7 = some (.success (.ctor 1 [.ctor 0 [.list [.ctor 2 [.some (.ctor 0 [.nat 0]),
  .ctor 0 [.list [.pair (.str "stack1") .unit, .pair (.str "stack0") .unit]]]]]]))
-- They are the stand-in version's answers, run by run.
#guard exitOf r2 = exitOf Test.Program.QueueScenarios.r2
#guard exitOf r5 = exitOf Test.Program.QueueScenarios.r5
#guard exitOf r7 = exitOf Test.Program.QueueScenarios.r7

/-! ## The added scenario: a taker under a masked caller

The caller masks the taker. An interrupt is requested while the taker waits. The request
stays pending: the taker stays registered, an offer's message reaches it, and it records the
message inside the caller's mask. The fiber is interrupted when the caller's mask ends. -/

/-- A masked caller's taker, with either `take`. The answer: the takers still registered
after the interrupt's request, the message the taker recorded, whether the taker's exit is an
interruption, and the buffer's size and the takers at the end. -/
def maskedCaller (takeOp : Ty → TermSrc → Src NativeOp) : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 2)
  let got ← Ref.make (nat 0)
  let f ← fork (uninterruptible (eff do
    let x ← takeOp .nat q
    Ref.set got x))
  let stop ← fork (withFiber (Action.interrupt f))
  let registered ← Ref.get q
  let _ ← offer .nat q (nat 9)
  let e ← await f
  let _ ← await stop
  let x ← Ref.get got
  let n ← size .nat q
  let s ← Ref.get q
  return tuple [Queue.len (field registered "takers"), x, app "causeIsInterrupt" [e], n,
    Queue.len (field s "takers")]

#guard verdict (maskedCaller take) = "built"

-- With the mask: the taker stays registered, gets the message 9, and is interrupted only
-- after its caller's mask. The buffer is empty, and no taker stays.
#guard exitOf (maskedCaller take) =
  some (.success (.list [.nat 1, .nat 9, .bool true, .nat 0, .nat 0]))

-- Red control: the stand-in `take` restores with `interruptible`, whatever its caller. Its
-- wait is interrupted under the masked caller: the taker withdraws, it records no message,
-- and the offered message stays in the buffer.
#guard exitOf (maskedCaller Test.Program.QueueScenarios.take) =
  some (.success (.list [.nat 0, .nat 0, .bool true, .nat 1, .nat 0]))

end Test.Program.QueueMask
