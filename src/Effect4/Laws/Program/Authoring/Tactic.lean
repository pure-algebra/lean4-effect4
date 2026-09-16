import Lean.Elab.Tactic

/-!
# Laws.Program.Authoring.Tactic — the scope discharge, goal-directed

Meta code only, and the one module of the authoring laws inside the gate's implementation
boundary (`Test/Audit/AxiomGate.lean`, `auditImplementationModules`): a tactic elaborator
reaches `Classical.choice` through Lean's own framework, and no theorem lives here.

`authoring_scoped` discharges `Src.Scoped` (or any authoring carrier's predicate) for a
program built from the lifts: each step reads the goal's head and applies the lemma named
after it (`f_scoped` for a lift or a piece of sugar `f`, the carrier's `cons`/`nil` and
`some`/`none` lemmas for a membership goal, the hypothesis for a variable), so no
alternative is ever tried against a goal it cannot close.
-/

namespace Effect4.Program.Authoring

open Lean Elab Tactic Meta in
/-- One step. A goal `∀ x ∈ l, C.Scoped x` applies the carrier's `cons`/`nil` (`some`/`none`)
lemma by the shape of `l`; any other Pi is introduced; a goal `C.Scoped (f …)` applies
`f_scoped`; a goal on a variable is its hypothesis. -/
elab "authoring_scoped_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
  let ty ← instantiateMVars (← goal.getType)
  let ty ← whnfR ty
  if ty.isForall then
    let body := ty.bindingBody!
    if body.isForall && body.bindingDomain!.isAppOf ``Membership.mem then
      let args := body.bindingDomain!.getAppArgs
      let coll ← whnfR args[args.size - 2]!
      let carrier := body.bindingBody!.getAppFn.constName!
      let suffix := if coll.isAppOf ``List.cons then "_cons"
        else if coll.isAppOf ``List.nil then "_nil"
        else if coll.isAppOf ``Option.some then "_some" else "_none"
      evalTactic (← `(tactic| apply $(mkIdent (carrier.appendAfter suffix))))
    else
      evalTactic (← `(tactic| intro))
    return
  let arg ← whnfR ty.getAppArgs.back!
  match arg.getAppFn with
  | .const f _ => evalTactic (← `(tactic| apply $(mkIdent (f.appendAfter "_scoped"))))
  | .fvar _ => evalTactic (← `(tactic| assumption))
  | _ => throwError "authoring_scoped: no lift at the head of {arg}"

/-- Discharge the scope predicate for a program built from the lifts. Unfold a named
program first (`unfold myProgram`), since the head must be a lift. -/
macro "authoring_scoped" : tactic => `(tactic| repeat' authoring_scoped_step)

end Effect4.Program.Authoring
