import Effect4.Api.Author
import Effect4.Program.Authoring.Loops
import Effect4.Codegen.Forms

/-! Verifier scratch: which part of the seat's pool is outside the printer's readable image.
Kept as the record of how the pool finding in `VerifyPrograms.lean` was located. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Verify.PoolRead
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- rc.112's `Effect.forkScoped` default, as the form table spells it (`Codegen/Forms.lean`,
`forkScopedDefault`). -/
def scopedDaemonOptions : Effect4.Supervision.ForkOptions := Effect4.Codegen.Forms.defaults true

def forkScopedWith (o : Effect4.Supervision.ForkOptions) : Module NativeOp :=
  { main := eff do
      let _ ← scope (eff do
        let _w ← withFiber (Action.forkScoped (succeed unit) o)
        succeed unit)
      succeed unit }

def releaseNamed : Module NativeOp :=
  { main := eff do
      let closes ← Ref.make (nat 0)
      scope (eff do
        let _conn ← acquireRelease "conn" "exit" (succeed unit) (Ref.update .incr closes)
        succeed unit) }

def readableOf (m : Module NativeOp) : Option Bool :=
  (Effect4.Api.Author.build m).toOption.map fun b => Effect4.Api.readable b.program b.table

#eval readableOf (forkScopedWith childOptions)
#eval readableOf (forkScopedWith scopedDaemonOptions)
#eval readableOf releaseNamed
#eval (childOptions.daemon, childOptions.startImmediately)
end Verify.PoolRead
