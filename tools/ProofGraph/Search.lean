import ProofGraph.Proof

namespace ProofGraph
open Lean Elab Meta

/-- Search is speculative. Only a closed term is returned, and all elaborator changes are
rolled back. Publishing it as evidence separately checks the term with the kernel. -/
def search (type : Expr) (tactic : Syntax) (cap : Nat) : TermElabM (Except String Expr) :=
  withoutModifyingState do
    tryCatchRuntimeEx
      (withOptions (fun o => maxHeartbeats.set o cap) <| withCurrHeartbeats do
        let goal ← mkFreshExprMVar type
        let rest ← Tactic.run goal.mvarId! (Tactic.evalTactic tactic)
        unless rest.isEmpty do return .error "search left goals open"
        let proof ← instantiateMVars goal
        if proof.hasMVar || proof.hasFVar || proof.hasSorry then
          return .error "search returned an open or admitted term"
        return .ok proof)
      (fun ex => return .error (← ex.toMessageData.toString))

/-- Trust dependencies of a candidate term, before it has a declaration name. -/
def axiomsOf (e : Expr) : CoreM (Array Name) := do
  let mut out : Array Name := #[]
  for c in e.getUsedConstants do
    for a in ← collectAxioms c do
      unless out.contains a do out := out.push a
  return out.qsort (·.toString < ·.toString)

/-- Publish the exact searched term as a kernel-checked theorem under the semantic ceiling. -/
def addTheorem (name : Name) (levels : List Name) (proposition proof : Expr) : MetaM ProofRef := do
  if proposition.hasMVar || proposition.hasFVar || proof.hasMVar || proof.hasFVar || proof.hasSorry then
    throwError "proof graph: cannot publish open evidence {name}"
  let extra := (← axiomsOf proof).filter fun a => ![``propext, ``Quot.sound].contains a
  unless extra.isEmpty do throwError "proof graph: {name} reaches disallowed axioms {extra}"
  addDecl <| .thmDecl {name, levelParams := levels, type := proposition, value := proof}
  let reference : ProofRef := ⟨name, levels, proposition⟩
  if let .error why ← reference.validate then throwError why
  return reference

end ProofGraph
