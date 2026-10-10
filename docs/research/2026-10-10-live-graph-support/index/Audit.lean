import Tools.Graph.Index
import Tools.View.FlowLaws
import ProofGraph.AxiomAudit

#axiom_audit Tools.Graph.Index Tools.View.FlowLaws

run_elab do
  let env ← Lean.getEnv
  let roots := [``Tools.View.Flow.relaxIndexed, ``Tools.View.Flow.assignHeightsIndexed,
    ``Tools.View.Flow.preparePlacement, ``Tools.View.Flow.relaxIndexed_agrees,
    ``Tools.View.Flow.assignHeightsIndexed_agrees, ``Tools.View.Flow.preparePlacement_height]
  let (results, _) := ProofGraph.reachedAxiomsMany env roots.toArray {}
  for (name, result) in roots.toArray.zip results do
    let some axioms := result | throwError "audit exhausted for {name}"
    for axiomName in axioms do
      unless [``propext, ``Quot.sound].contains axiomName do
        throwError "{name} reaches {axiomName}"
    Lean.logInfo m!"{name}: {axioms}"
