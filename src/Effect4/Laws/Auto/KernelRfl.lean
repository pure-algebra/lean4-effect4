import Lean.Elab.Tactic

/-!
# Kernel reflexivity for equations with free values

The tactic assigns `Eq.refl` without the elaborator's definitional equality check.
The kernel checks the declaration. A false equation receives a kernel type error.
Consumers: the crews' static program equations and the host-protocol scenario equations.
The tactic adds no axiom and admits no equation that the kernel refuses.
-/

namespace Effect4.Laws.Auto

/-- Assign reflexivity and require the kernel to check the declaration's equation. -/
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

end Effect4.Laws.Auto
