import Effect4
import Effect4.Laws
import Effect4.Laws.Library.PartitionedSemaphore.Steps
import Test.Program.PartitionedSemaphoreBookkeeping
import Test.Program.PartitionedSemaphoreFaces
import ProofGraph.Audit
import ProofGraph.Goal
import ProofGraph.Registry
import Tools.LoadPaths

open Lean Elab Command

elab "#bookkeeping_audit" : command => do
  let env ← getEnv
  let modules := #[`Effect4.Library.PartitionedSemaphore.Model,
    `Effect4.Library.PartitionedSemaphore.Cell, `Effect4.Library.PartitionedSemaphore.Data,
    `Effect4.Library.PartitionedSemaphore.Steps, `Effect4.Laws.Library.PartitionedSemaphore.Data,
    `Effect4.Laws.Library.PartitionedSemaphore.Steps,
    `Test.Program.PartitionedSemaphoreBookkeeping, `Test.Program.PartitionedSemaphorePrograms,
    `Test.Program.PartitionedSemaphoreFaces]
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
  let coreClosure := ProofGraph.Audit.moduleImportClosure graph `Effect4
  let lawClosure := ProofGraph.Audit.moduleImportClosure graph `Effect4.Laws
  for n in coreClosure do
    if (`Effect4.Laws).isPrefixOf n then throwError "core root reaches Laws: {n}"
  for m in modules do
    if (`Effect4.Library.PartitionedSemaphore).isPrefixOf m && !coreClosure.contains m then
      throwError "new core module is unreachable: {m}"
    if (`Effect4.Laws.Library.PartitionedSemaphore).isPrefixOf m && !lawClosure.contains m then
      throwError "new law module is unreachable: {m}"
  let (testImports, _, _) ← Lean.Elab.parseImports (← IO.FS.readFile "Test/All.lean")
  for m in modules do
    if (`Test.Program).isPrefixOf m && !testImports.any (·.module == m) then
      throwError "new battery is not registered in Test.All: {m}"
  let claimName := `Effect4.PartitionedSemaphore.Model.bookkeeping_agrees
  let claims := Tools.Semantics.registry.claims.filter (·.id == "partitioned-semaphore-bookkeeping")
  unless claims.length == 1 do throwError "missing or duplicate claim"
  for claim in claims do
    unless claim.concept == "translation-simulation" && claim.role == .simulation do
      throwError "wrong claim placement"
    match claim.pointer with
    | .witness name => unless name == claimName do throwError "wrong registry pointer"
    | _ => throwError "claim has no theorem pointer"
  let (standing, _) := (ProofGraph.standing env claimName).run {}
  match standing with
  | some (.proved, _) => pure ()
  | _ => throwError "claim is not proved without open goals"
  logInfo m!"PASS bookkeeping: {facts.size} compiled declarations, permitted axioms only, core/law boundary, exact registry pointer, no open claim goals"

#bookkeeping_audit
#load_report Effect4.Laws.Library.PartitionedSemaphore
