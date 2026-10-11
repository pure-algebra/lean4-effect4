import Effect4.Api
import Effect4.Api.Author

/-!
# `E4-RUN-CE-046`: self-interruption after local write-back

The admitted program passes the child its own handle through a deferred.
On rc.112, the child exits interrupted before writing the log.
The retained pin evaluation returns an interrupted exit and log zero.
The machine now retains the addressed interrupt through the local write-back.
The regression checks the same observation at budget 20000.
The ordinary other-child interrupt remains a separate control.

This is finite evaluation evidence for the R2 repair.
It establishes no universal runtime correspondence or progress claim.
The message order remains local write-back, addressed edits, owner lookup, then disposition.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Counterexamples.Machine.Semantics.SelfInterrupt

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- The root's exit at budget 20000, on the ordinary run, or `none` if the build refuses. -/
def exitOf (src : Src NativeOp) : Option (Option ExitV) :=
  (Effect4.Api.Author.build { main := src }).toOption.map fun b => (Api.run b.program 20000).exit

/-- The child learns its own handle from a deferred that the parent completes, interrupts itself,
then would write its log. -/
def selfByHandle : Src NativeOp := eff do
  let d ← Deferred.make (.fiberOf .nat .never) .never
  let log ← Ref.make (nat 0)
  let f ← fork (eff do
    let me ← Deferred.await d
    let _ ← withFiber (Action.interrupt me)
    let _ ← Ref.update "l" (app "add" [var "l", nat 1]) log
    succeed (nat 1))
  let _ ← Deferred.succeed d f
  let e ← await f
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

/-- The control: the parent interrupts a parked child. -/
def other : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let f ← fork (Deferred.await d)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  return app "causeIsInterrupt" [e]

-- The repaired regression: the child exits interrupted before its log write.
#guard exitOf selfByHandle = some (some (.success (.list [.bool true, .nat 0])))

-- The control: an interrupt of another fiber reaches it.
#guard exitOf other = some (some (.success (.bool true)))

end Test.Counterexamples.Machine.Semantics.SelfInterrupt
