import Test.Audit.ProofGraph

#print axioms ProofGraph.disallowedAxioms
#print axioms Test.ProofGraph.polymorphicGoal
#print axioms Test.ProofGraph.polymorphicWitness
#print axioms Test.ProofGraph.nestedMarker
#print axioms Test.ProofGraph.allowedPropext

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  if (← getEnv).contains `Test.ProofGraph.forbiddenPlaceholder then
    throwError "negative fixture leaked its temporary declaration"
