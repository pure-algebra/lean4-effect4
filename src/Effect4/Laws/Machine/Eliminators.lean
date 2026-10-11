import Lean.Elab.Command
import Lean.Meta.Match.MatchEqs
import Effect4.Machine.Fibers

/-!
Concept: reactive-scheduling R11, serving the native evaluator classifications.
Consumers: NativeExecutor and Guard.ReturnCommands use the evaluator's generated cases.
Lean realizes these eliminators and matcher equalities once for both consumers.
This module adds no evaluator, syntax, or behavioral claim.
-/

run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.realizeGlobalConstNoOverloadCore `Effect4.Machine.evaluatePrim.fun_cases
  discard <| Lean.realizeGlobalConstNoOverloadCore `Effect4.Machine.evaluatePrim.withFiber.fun_cases
  let names := (← Lean.getEnv).constants.toList.map Prod.fst
  for name in names do
    if (`Effect4.Machine.evaluatePrim).isPrefixOf name then
      if (← Lean.Meta.getMatcherInfo? name).isSome then
        discard <| Lean.Meta.Match.genMatchCongrEqns name
