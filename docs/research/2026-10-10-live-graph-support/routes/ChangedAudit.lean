import Tools.View.Graph
import ProofGraph.AxiomAudit

open Lean Elab Command

-- Use the same cycle-aware walk as #axiom_audit on every changed declaration.
run_elab do
  let env ← getEnv
  let roots := #[``Tools.View.Laid.segmentDescends, ``Tools.View.Laid.downRouteDescends,
    ``Tools.View.Laid.downRouteDescends_iff, ``Tools.View.Laid.edgesDescend,
    ``Tools.View.Laid.edgesDescend_down_pairs]
  let (results, _) := ProofGraph.reachedAxiomsMany env roots {} (ProofGraph.isGoal env)
  for (name, result) in roots.zip results do
    match result with
    | none => throwError "{name}: axiom walk exhausted its budget"
    | some reached =>
      let outside := reached.filter (!ProofGraph.trustedAxioms.contains ·)
      unless outside.isEmpty do
        throwError "{name}: outside trusted axioms {outside}"
      logInfo m!"CHANGED AXIOMS {name}: {reached}"
