import Effect4.Run
import Effect4.Api.Author
import Effect4.Program.Typing.Call
open Effect4 Effect4.Machine Effect4.Program
-- Candidate reachable witness for proposed rows-block-host scheduler invariant.
def identityRow : Row :=
 {name := "probeIdentity", spelling := "probeIdentity", kind := .async, registration := .external,
  request := .var 0, answer := .var 0, cite := "PROC6 review probe"}
def program : NativeEff :=
 .bind (.withFiber (.context .empty))
   (.bind (.perform (.external 0) (.var 0))
     (.provideContext (.var 1) (.sync (.lit .unit))))
#eval admitSig ⟨[identityRow], []⟩
#eval (typeOfProgram (SigApp.signature ⟨[identityRow], []⟩) program).isSome
#eval (admitProgram program ⟨[identityRow], []⟩).isOk
#eval (callAt (SigApp.signature ⟨[identityRow], []⟩) [] program [1,0]).any (fun c => c.answer == .contextOf .empty)
def poison : Ctx := Ctx.withServices ((Env.Context.empty : Env.Ctx).addV Env.maxOpsKey (.nat 1))
def checkedRun : Option Run := do
 let built ← (Api.Author.Internal.finishBuild program [identityRow] []).toOption
 let run := (Run.open built "proc6" {fuel := 500, compileFuel := 100}).control Api.evaluate
 let await ← run.outstanding.head?
 pure (run.answer ⟨await.fiber, await.token⟩ (.ofExit (.success (Val.context poison))))
#eval checkedRun.map fun r => (r.outstanding.length, r.machine.trace.length,
  r.machine.fibers.map (fun f => (f.maxOpsBeforeYield, f.preventYield, f.context.maxOpsBeforeYield)))
