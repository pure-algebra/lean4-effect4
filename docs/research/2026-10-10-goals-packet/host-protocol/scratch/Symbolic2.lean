import Test.Dogfood.Scenario.Timeout

/-! The kernel on `fetch`'s run with a free reply body. A finite probe. -/

open Effect4 Effect4.Machine Test.Dogfood.Scenario Test.Dogfood.Scenario.Timeout

set_option maxRecDepth 100000
set_option maxHeartbeats 0

syntax (name := kernelRfl) "kernel_rfl" : tactic

open Lean Elab Tactic Meta in
@[tactic kernelRfl] def evalKernelRfl : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  match ty.consumeMData.eq? with
  | some (_, lhs, _) =>
    goal.assign (← mkEqRefl lhs)
    replaceMainGoal []
  | none => throwError "kernel_rfl: the goal is not an equation"

-- the reply before the timeout, with a free body: the root answers that body
set_option trace.profiler true in
theorem free_body (body : String) :
    (Effect4.Api.Author.build fetch).toOption.map
      (fun b => (observe (Test.Dogfood.Scenario.play (opened b)
        (parked ++ answer http (ok (.str body))))).root) =
      some (.answered (.str body)) := by
  kernel_rfl
