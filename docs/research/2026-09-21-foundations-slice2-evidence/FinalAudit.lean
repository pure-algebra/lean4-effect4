import Effect4.Laws
import Test.Counterexamples.Machine.Semantics.ActionAtRaceAllPremise
open Lean Meta Elab Command ProofGraph
#obligation_audit Effect4
run_cmd liftTermElabM do
  let env ← getEnv
  let mut goals : Array Goal := #[]
  let mut entries : Array Entry := #[]
  for (name, info) in env.constants.toList do
    if (`Effect4).isPrefixOf name then
      let goal? ← forallTelescope info.type fun xs body => do
        if body.isAppOfArity ``Obligation 1 then
          return some (⟨name, info.levelParams, ← mkForallFVars xs body.appArg!, #[]⟩ : Goal)
        return none
      if let some goal := goal? then
        goals := goals.push goal
        let checked := name ++ `checked
        if env.contains checked then
          unless !env.contains (name ++ `wanted) do throwError "stale marker {name}"
          entries := entries.push ⟨name, .proved checked⟩
        else
          entries := entries.push ⟨name, .wanted (name ++ `wanted)⟩
          logInfo m!"OPEN {name}"
  let report ← ProofGraph.check goals entries 10
  logInfo m!"UNIQUE LEDGER: {goals.size} total; {report.proved} proved; {report.wanted} open"

#print Effect4.Program.Typed.Preds
#print Effect4.Program.Typed.TaskOk
#print Effect4.Program.Typed.CmdOk
#print Effect4.Program.Typed.RSavedOk
#print Effect4.Program.Typed.CaptureOk
#print Effect4.Program.Typed.RSavedOk.frame_interruptible
#print Effect4.Program.Typed.CaptureOk.frame_root
#print Effect4.Program.Typed.Contracts.FrameAccepts
#print Effect4.Program.Typed.Contracts.StackAccepts
#print Effect4.Program.Typed.Contracts.SavedOk
#print Effect4.Program.Typed.Contracts.ResumeOk
#print axioms Effect4.Program.Typed.Contracts.Example.changing_middle
#print axioms Effect4.Program.Typed.Contracts.Example.middle_differs
#print axioms Effect4.Program.Typed.order_refl
#print axioms Effect4.Program.Typed.order_trans
#print axioms Effect4.Program.Typed.fork_extension
#print axioms Effect4.Program.Typed.refMake_extension
#print axioms Effect4.Program.Typed.deferredMake_extension
#print axioms Effect4.Program.Typed.memoBuild_extension
#print axioms Effect4.Program.Typed.RSavedOk.frame_interruptible
#print axioms Effect4.Program.Typed.CaptureOk.frame_root
