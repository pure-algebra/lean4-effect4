import Test.Program.QueueScenariosData
import Effect4.Program.Authoring.Mask

/-! Program data shared by the battery and engine fixture writer. -/

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

/-- The earlier slice's operations: the masked `take`, and the stand-in `offer`. -/
def mixed : Ops :=
  { take := Written.take Written.restoring, offer := Written.offer Written.standIn,
    size := Written.size }

end Test.Program.QueueMask
