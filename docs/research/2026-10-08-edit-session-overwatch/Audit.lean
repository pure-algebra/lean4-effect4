import Effect4
import Effect4.Laws.Program.Edit
import Test.Program.EditControls
import ProofGraph.Audit
import ProofGraph.Goal
import ProofGraph.Registry

/-! Scoped compiled audit for the edit-session review at fdbae937.
This audits the newly added modules, their compiled auxiliaries and the touched splice law module.
It checks the three exact registered pointers and their goal-free standing.
It is not the whole-tree axiom gate. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules := #[`Effect4.Program.Edit, `Effect4.Laws.Program.Edit,
    `Effect4.Laws.Program.Typing.Splice, `Test.Program.EditControls]
  let (facts, byModule, missing) := ProofGraph.Audit.auditedFacts env modules.contains
  unless missing.isEmpty do throwError "missing compiled declarations: {missing}"
  for m in modules do
    let names := byModule.getD m #[]
    unless names.size > 0 do throwError "absent or empty audited module: {m}"
    logInfo m!"audited {m}: {names.size} declarations"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque || fact.hasInitFn then
        throwError "forbidden compiled body: {fact.name}"
  let (results, _) := ProofGraph.reachedAxiomsMany env (facts.map (·.name)) {}
  for (fact, result) in facts.zip results do
    let some axioms := result | throwError "axiom walk exhausted: {fact.name}"
    for ax in axioms do
      unless #[`propext, `Quot.sound].contains ax do
        throwError "unexpected axiom: {fact.name} -> {ax}"
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n,d) =>
    (n, d.imports.map (·.module))
  let closure := ProofGraph.Audit.moduleImportClosure graph `Effect4
  unless closure.contains `Effect4.Program.Edit do throwError "core root omits Edit"
  for n in closure do
    if (`Effect4.Laws).isPrefixOf n then throwError "core root reaches Laws: {n}"
  let expected := #[
    ("edit-session-coherent", `Effect4.Program.EditSession.reached_view),
    ("edit-session-undo", `Effect4.Program.EditSession.feed_undo),
    ("edit-repaint-set", `Effect4.Program.EditSession.feed_repaint)]
  for (id, name) in expected do
    let claims := Tools.Semantics.registry.claims.filter (·.id == id)
    unless claims.length == 1 do throwError "missing or duplicate claim: {id}"
    for claim in claims do
      unless claim.concept == "initial-algebras-folds" do throwError "wrong concept: {id}"
      match claim.pointer with
      | .witness found => unless found == name do throwError "wrong pointer: {id}"
      | _ => throwError "claim lacks witness: {id}"
    let (standing, _) := (ProofGraph.standing env name).run {}
    match standing with
    | some (.proved, _) => logInfo m!"proved without open goals: {id} -> {name}"
    | _ => throwError "claim rests on an open goal: {id}"
  logInfo m!"PASS: {facts.size} compiled declarations within [propext, Quot.sound]; core/law import boundary; three exact goal-free claim pointers"
