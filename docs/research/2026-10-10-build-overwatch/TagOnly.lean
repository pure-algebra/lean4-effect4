import ProofGraph.GoalTag

open Lean Elab Command
run_cmd do
  let env ← getEnv
  unless (env.getModuleIdx? `ProofGraph.Axioms).isNone do
    throwError "the tag imports the axiom walk"
  unless (env.getModuleIdx? `ProofGraph.Goal).isNone do
    throwError "the tag imports the standing walk"
