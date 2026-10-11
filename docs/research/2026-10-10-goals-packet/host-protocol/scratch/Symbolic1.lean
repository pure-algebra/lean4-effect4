import Test.Dogfood.Scenario.Routing

/-! Which parts of the escape run the kernel computes with free values. A finite probe. -/

open Effect4 Effect4.Machine Test.Dogfood.Scenario Test.Dogfood.Scenario.Routing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Close an equation by the kernel's definitional check alone: the goal is assigned
`Eq.refl lhs` unchecked, and the kernel checks the declaration. No axiom; `decide +kernel`
does the same for a closed decision. -/
syntax (name := kernelRfl) "kernel_rfl" : tactic

open Lean Elab Tactic Meta in
@[tactic kernelRfl] def evalKernelRfl : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  match ty.eq? with
  | some (_, lhs, _) =>
    goal.assign (← mkEqRefl lhs)
    replaceMainGoal []
  | none => throwError "kernel_rfl: the goal is not an equation"

/-- The escape run's outcome, at a request and a failure. -/
def outcomeOf (token : String) (id : Nat) (idText tag message : String) : Option (Option ExitV) :=
  (Effect4.Api.Author.build (request token id idText)).toOption.map fun b =>
    (observe (Test.Dogfood.Scenario.play (opened b) (failing tag message))).outcome

-- 2. a free message: the kernel's definitional check
set_option trace.profiler true in
theorem free_message (message : String) : outcomeOf "secret" 2 "2" "SqlError" message =
    some (some (.failure (Cause.fail (.tagged "SqlError" message)))) := by
  kernel_rfl

-- 3. a free id and id text, and a free message
set_option trace.profiler true in
theorem free_request (id : Nat) (idText message : String) :
    outcomeOf "secret" id idText "SqlError" message =
      some (some (.failure (Cause.fail (.tagged "SqlError" message)))) := by
  kernel_rfl

#print axioms free_request
