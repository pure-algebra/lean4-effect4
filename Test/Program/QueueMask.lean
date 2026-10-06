import Test.Program.QueueScenarios
import Effect4.Program.Authoring.Mask

/-!
# The Queue's `take` under a masked caller (decisions rows 222, 244 to 246 and 251)

The library's operations hold the mask that restores (`src/Effect4/Modules/Waiting.lean`). Under
an interruptible caller the wait is interruptible. Under a masked caller the restore is the
identity: the request stays registered, it may consume, and the fiber is interrupted when its
caller's mask ends. `Test/Program/QueueScenarios.lean` runs the eight scenarios, where no caller
is masked. This battery adds the scenario of a masked caller.

The red control is the earlier fixture's form, with its two stand-ins
(`Written.standIn`): it restores with `interruptible`, whatever its caller, so its wait is
interrupted under the masked caller.

**The earlier slice's own programs.** Seat MASK's battery ran R2, R5, R7 and the masked caller
with a masked `take` and the stand-in `offer` (`mixed` below). The library's `offer` holds the
mask too. So the library's program is the earlier one in R7, which takes only, and it differs by
the offer's mask in the other three.

Placement. Each scenario is a finite control of the claim `saved-mask-restoration` (concept
`scope-lifetime-finalization`, requirement R11) on the side of one client, and of the proposed
claim `waiting-request-obligation-preserved` (concept `reactive-scheduling`): an interruption
that is only requested, and stays pending under a mask, withdraws nothing. Every guard is one
run on one schedule. None proves delivery or liveness, none is a host run, and the mask's laws
name no declaration of the Queue. Under a masked caller the form's exit flag is tested here, and
no theorem states it: the mask's invariant of runs is an open part of R11.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueMask

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios
open Effect4.Modules

/-! ## The scenario: a taker under a masked caller

The caller masks the taker. An interrupt is requested while the taker waits. The request
stays pending: the taker stays registered, an offer's message reaches it, and it records the
message inside the caller's mask. The fiber is interrupted when the caller's mask ends. -/

/-- A masked caller's taker, over one set of operations. The answer: the takers still registered
after the interrupt's request, the message the taker recorded, whether the taker's exit is an
interruption, and the buffer's size and the takers at the end. -/
def maskedCallerWith (ops : Ops) : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let got ← Ref.make (nat 0)
  let f ← fork (uninterruptible (eff do
    let x ← ops.take .nat q
    Ref.set got x))
  let stop ← fork (withFiber (Action.interrupt f))
  let registered ← Ref.get q
  let _ ← ops.offer .nat q (nat 9)
  let e ← await f
  let _ ← await stop
  let x ← Ref.get got
  let n ← ops.size .nat q
  let s ← Ref.get q
  return tuple [len (field registered "takers"), x, app "causeIsInterrupt" [e], n,
    len (field s "takers")]

/-- The masked caller over the library's operations. -/
def maskedCaller : Src NativeOp := maskedCallerWith library

#guard verdict maskedCaller = "built"

-- With the mask: the taker stays registered, gets the message 9, and is interrupted only
-- after its caller's mask. The buffer is empty, and no taker stays.
#guard exitOf maskedCaller =
  some (.success (.list [.nat 1, .nat 9, .bool true, .nat 0, .nat 0]))
-- The ordinary run gives the same answer at the truth lane's fuel.
#guard exitAt 1000 maskedCaller = exitOf maskedCaller

-- Red control: the stand-in `take` restores with `interruptible`, whatever its caller. Its
-- wait is interrupted under the masked caller: the taker withdraws, it records no message,
-- and the offered message stays in the buffer.
#guard exitOf (maskedCallerWith (Written.ops Written.standIn)) =
  some (.success (.list [.nat 0, .nat 0, .bool true, .nat 1, .nat 0]))

/-! ## The trees: the library's program against the written forms -/

-- The library's program has the bytes of the written forms under the mask that restores.
#guard bytesOf maskedCaller == bytesOf (maskedCallerWith (Written.ops Written.restoring))
#guard (bytesOf maskedCaller).isSome

/-- The earlier slice's operations: the masked `take`, and the stand-in `offer`. -/
def mixed : Ops :=
  { take := Written.take Written.restoring, offer := Written.offer Written.standIn,
    size := Written.size }

-- R7 takes only, so the library's program is the earlier slice's program.
#guard bytesOf r7 == bytesOf (r7With mixed)
-- R2, R5 and the masked caller offer too: the library's program differs from the earlier one,
-- by the offer's mask, and it gives the earlier answer.
#guard [r2With, r5With, maskedCallerWith].all fun scenario =>
  bytesOf (scenario library) != bytesOf (scenario mixed) &&
    exitOf (scenario library) == exitOf (scenario mixed)

end Test.Program.QueueMask
