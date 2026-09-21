import Effect4.Laws
open Lean Meta Elab Command
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
run_cmd liftTermElabM do
  let env ← getEnv
  let names := env.constants.toList.map (·.1) |>.filter ((`Effect4).isPrefixOf ·)
    |>.toArray.qsort (·.toString < ·.toString)
  for n in names do
    let ci ← getConstInfo n
    forallTelescope ci.type fun xs body => do
      if body.isAppOfArity ``ProofGraph.Obligation 1 then
        let proposition ← mkForallFVars xs body.appArg!
        logInfo m!"STATEMENT {n} {← ppExpr proposition}"
