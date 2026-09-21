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


#print axioms Effect4.Laws.Effects.Typed.mono
#print axioms Effect4.Laws.Effects.Typed.bind
#print axioms Effect4.Laws.Effects.Typed.widen
#print axioms Effect4.Laws.Effects.Typed.inl
#print axioms Effect4.Laws.Effects.Typed.inl_inv
#print axioms Effect4.Laws.Effects.Typed.inr_inv
#print axioms Effect4.Laws.Effects.Typed.pure_inv
#print axioms Effect4.Laws.Effects.Typed.plain_iff
#print axioms Effect4.Machine.refWriteBack_peek_other
#print axioms Effect4.Machine.indexed_ref_step_preserves
#print axioms Effect4.Machine.Refinement.projects_compose
#print axioms Effect4.Machine.Refinement.projects_induces_refines
