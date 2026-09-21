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
  let report ← ProofGraph.check goals entries 9
  logInfo m!"UNIQUE LEDGER: {goals.size} total; {report.proved} proved; {report.wanted} open"


#print axioms Effect4.Program.Typed.park_extension
#print axioms Effect4.Program.Typed.valid_refMake_fresh
#print axioms Effect4.Program.Typed.valid_deferredMake_fresh
#print axioms Effect4.Program.Typed.valid_nextToken_fresh
#print axioms Effect4.Program.Typed.ref_completion_live
#print axioms Effect4.Program.Typed.leHost_refl
#print axioms Effect4.Program.Typed.leHost_trans
#print axioms Effect4.Program.Typed.leHost_base
#print axioms Effect4.Program.Typed.value_transport
#print axioms Effect4.Program.Typed.completion_transport
#print axioms Effect4.Program.Typed.valueOk_mono
#print axioms Effect4.Program.Typed.completionOk_mono
#print axioms Effect4.Program.Typed.heapTypedAt_mono
#print axioms Effect4.Program.Typed.promiseTypedAt_mono
#print axioms Effect4.Program.Typed.exitFits_mono
#print axioms Effect4.Program.Typed.initial_world_valid
