import Effect4.Api
import Effect4.Api.Author

/-!
# `E4-RUN-CE-046`: a fiber that interrupts itself through its own handle loses the interrupt (seeded)

rc.112's `fiberInterruptAs` calls the target's `interruptUnsafe`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`). On a running interruptible target it records
the cause and sets `_deferredInterrupt`, so the target fails with the interrupt at its next loop
top. The machine's `interruptAs` arm (`RunMachine` `evaluatePrim`'s `withFiber`,
`src/Effect4/Machine/Fibers.lean`) records on the target's stored record. When the target is the
running fiber, that stored record is a stale copy: `settle` writes the running fiber's own copy back
over it, and the interrupt is lost. The arm's `afterInterrupt` then parks the fiber on a join of
its own exit, so the run stops at a frontier.

The program passes the build: a parent hands the child its own handle through a deferred. On the
pin (`effect` 4.0.0-rc.112 under bun, `harness/truth/node_modules`, 2026-10-11) the same program
answers `[Failure(Interrupt(fiberId 2)), 0]`: the child exits interrupted by itself before its log
write. The witness below is the machine's run at budget 20000: no exit. The control is an ordinary
interrupt of a parked child. The forced repair: an edit of another fiber's record is applied after
the running fiber's write-back, so an edit of the running fiber itself reaches it
(`docs/research/2026-10-11-machine-models/README.md`).
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

-- The attack: the program is admitted, and the run has no exit. rc.112 answers [true, 0].
#guard exitOf selfByHandle = some none

-- The control: an interrupt of another fiber reaches it.
#guard exitOf other = some (some (.success (.bool true)))

end Test.Counterexamples.Machine.Semantics.SelfInterrupt
