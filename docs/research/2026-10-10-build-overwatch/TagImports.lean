import Test.Audit.SemanticsCensus
import Test.Audit.Obligations
import ProofGraph.Goal

open Lean Elab Command ProofGraph Effect4.Laws.Auto

run_cmd liftTermElabM do
  let env ← getEnv
  let ns := `Test.Audit.SemanticsCensus
  for (name, expected) in
      [(ns ++ `wantedGoal, Standing.goal),
       (ns ++ `restingWitness, .modulo #[ns ++ `wantedGoal]),
       (ns ++ `placedGoal, .goal),
       (ns ++ `placedSketch, .modulo #[ns ++ `placedSketch.part1]),
       (ns ++ `placedWitness, .proved)] do
    let some (status, axioms) := ((standing env name).run {}).1
      | throwError "the imported standing ran out of budget"
    unless status == expected && axioms.isEmpty do
      throwError "the imported standing changed: {name}"
  for name in [ns ++ `placedGoal, ns ++ `placedWitness, ns ++ `placedSketch.part1] do
    let some placement := semanticsAttribute.getParam? env name
      | throwError "an imported placement disappeared"
    unless placement.requirement == some "R2" && placement.concept == "fixture-two" do
      throwError "an imported placement changed"
  unless semanticsModule env ``ProofGraph.tagGoal == `ProofGraph.GoalTag do
    throwError "the goal command is not owned by its extracted module"
  unless semanticsModule env ``ProofGraph.standing == `ProofGraph.Goal do
    throwError "the standing walk moved into the tag module"
