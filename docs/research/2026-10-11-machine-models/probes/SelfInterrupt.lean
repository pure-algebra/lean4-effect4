import Effect4.Api
import Effect4.Api.Author

/-!
A probe: a fiber that interrupts itself through its own handle.

rc.112 `fiberInterruptAs` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, `interruptUnsafe`):
a running interruptible target records the cause and sets `_deferredInterrupt`, so the fiber
fails with the interrupt at its next loop top. The machine's `interruptAs` records on the stored
copy of the target, and `settle` writes the running fiber's local copy back over it.
-/

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def run (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .error (.typing r) => s!"refused, typing: {r.reason.head}"
  | .error (.scope _) => "refused: scope"
  | .error (.admission _) => "refused: admission"
  | .error _ => "refused"
  | .ok b =>
    let r := Api.run b.program 20000
    match r.exit with
    | none => "no exit: the run stops at a frontier"
    | some (.success v) => s!"success {repr v}"
    | some (.failure _) => "failure"

/-- The root interrupts itself, then would answer 1. -/
def selfRoot : Src NativeOp := eff do
  let me ← withFiber Action.getId
  let _ ← withFiber (Action.interrupt me)
  succeed (nat 1)

/-- A forked child interrupts itself; the parent awaits it and reads whether it was interrupted. -/
def selfChild : Src NativeOp := eff do
  let f ← fork (eff do
    let me ← withFiber Action.getId
    let _ ← withFiber (Action.interrupt me)
    succeed (nat 1))
  let e ← await f
  return app "causeIsInterrupt" [e]

/-- The child learns its own handle from a deferred that the parent completes, then interrupts
itself while it runs. rc.112: the child fails with its own interrupt. -/
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

#eval IO.println s!"selfRoot:  {run selfRoot}"
#eval IO.println s!"selfChild: {run selfChild}"
#eval IO.println s!"selfByHandle: {run selfByHandle}"
#eval IO.println s!"other:     {run other}"
