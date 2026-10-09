import Effect4.Laws.Program.Sketch
import ProofGraph.Audit
import ProofGraph.Axioms

/-! Scoped imported-module trust check with the existing gate helpers.
The audited module list is exact. This is not the whole-tree gate. -/

open Lean Elab Command

elab "#s1_scoped_audit" : command => do
  let environment ← getEnv
  let modules := #[`Effect4.Laws.Program.Sketch, `Effect4.Laws.Program.Typing.Parts]
  let (facts, byModule, missing) := ProofGraph.Audit.auditedFacts environment modules.contains
  unless missing.isEmpty do
    throwError "S1 scope: missing declarations {missing}"
  for m in modules do
    unless (byModule.getD m #[]).size > 0 do
      throwError "S1 scope: empty module {m}"
  for fact in facts do
    if !fact.safeRecursor then
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque then
        throwError "S1 scope: forbidden declaration form {fact.name}"
  let declarations := facts.map (·.name)
  let (reachedAll, _) := ProofGraph.reachedAxiomsMany environment declarations {}
  let allowed := #[``propext, ``Quot.sound]
  let mut reachedUnion : Array Name := #[]
  for (declaration, reached) in declarations.zip reachedAll do
    let some axioms := reached
      | throwError "S1 scope: axiom budget exhausted at {declaration}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "S1 scope: {declaration} reaches forbidden axiom {ax}"
      if !reachedUnion.contains ax then reachedUnion := reachedUnion.push ax
  for m in modules do
    logInfo m!"S1 scoped trust: {m}: {(byModule.getD m #[]).size} declarations audited"
  logInfo m!"S1 scoped trust: {declarations.size} declarations; missing {missing.size}; transitive axioms {reachedUnion}"

#s1_scoped_audit
