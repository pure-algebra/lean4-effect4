import Tools.Explain
import ProofGraph.Axioms

/-!
Finite environment audit of the C3 relocation at base 01c83fbc.
Concept: translation-simulation. Claim consumer: row 332's library cutover trust gate.
Reach: axioms of the existing Tools.Explain declarations before their planned move.
Limits: no semantic theorem, no relocated build, no runtime or whole-tree acceptance.
Consumer: C3 must give moved instrumentation its exact audit treatment.
-/

open Lean Elab Command

elab "#cutover_explain_axioms" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if env.header.moduleNames[idx.toNat]! == `Tools.Explain then
      roots := roots.push n
  roots := roots.qsort (·.toString < ·.toString)
  let (all, _) := ProofGraph.reachedAxiomsMany env roots {}
  let mut bad : Array Name := #[]
  for (n, reached) in roots.zip all do
    let some axioms := reached | throwError "inconclusive axiom traversal: {n}"
    if axioms.contains ``Classical.choice then bad := bad.push n
  logInfo m!"Tools.Explain: {roots.size} declarations; {bad.size} reach Classical.choice"
  for n in bad do logInfo m!"choice: {n}"
  for n in #[`Tools.Explain.canonicalJson, `Tools.Explain.schemaText,
      `Tools.Explain.render, `Tools.Explain.explain, `Tools.Explain.Explanation.text,
      `Tools.Explain.elabExplain] do
    let (reached, _) := (ProofGraph.reachedAxioms env n).run {}
    logInfo m!"{n}: {reached}"

#cutover_explain_axioms
