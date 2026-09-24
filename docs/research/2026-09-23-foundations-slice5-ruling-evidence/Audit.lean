import Effect4.Laws
import Test.Program.TypedControl

/-! Production obligation scope, matching the foundations receipts. The full
module-closure and axiom gate runs separately in the `Test.All` build. Importing
that test root here also includes two test-only obligations under `Effect4`. -/

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

-- Inspect every compiled declaration of the new counterexample module, including auxiliaries.
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if [`Test.Counterexamples.Machine.Semantics.AsyncHookContract, `Test.Program.TypedControl].contains (env.header.moduleNames[idx.toNat]?.getD .anonymous) then
        let axioms ← Lean.collectAxioms name
        unless axioms.toList.all (fun n => n == `propext || n == `Quot.sound) do
          throwError "unexpected axiom dependency {name}: {axioms.toList}"
        count := count + 1
        logInfo m!"COUNTEREXAMPLE AXIOMS {name}: {axioms.toList}"
  logInfo m!"COUNTEREXAMPLE AND CONTROL MODULES: {count} declarations checked at [propext, Quot.sound]"
