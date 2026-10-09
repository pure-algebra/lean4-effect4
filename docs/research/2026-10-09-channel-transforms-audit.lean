import Effect4.Library
import Test.Program.Channel
import Test.Program.ModuleDeclarations
import Effect4.Laws.Library.Channel.Protocol
import Effect4.Laws.Library.Stream.Definitions
import ProofGraph.Audit
import ProofGraph.Axioms
import ProofGraph.ProofStyle
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

run_meta do
  let targets : Array Name := #[`Effect4.Program.Authoring.Module,
    `Effect4.Library.Channel.Ops, `Effect4.Laws.Library.Channel.Scope,
    `Effect4.Laws.Library.Channel.Protocol, `Effect4.Library.Stream.Definitions,
    `Effect4.Laws.Library.Stream.Definitions,
    `Test.Program.Channel, `Test.Program.ModuleDeclarations]
  let env ← getEnv
  let (facts, _, missing) := ProofGraph.Audit.auditedFacts env targets.contains
  unless missing.isEmpty do throwError "missing declarations: {missing}"
  for fact in facts do
    unless fact.safeRecursor do
      if fact.isUnsafe || fact.isPartial || fact.isAxiom || fact.isExtern ||
          fact.implementedBy || fact.bodilessOpaque then
        throwError "forbidden declaration shape: {fact.name}"
  let names := facts.map (·.name)
  let (results, _) := ProofGraph.reachedAxiomsMany env names {}
  for target in targets do
    let mut count : Nat := 0
    for i in [:names.size] do
      let name := names[i]!
      if ProofGraph.Audit.moduleOf? env name == some target then
        count := count + 1
        let some axioms := results[i]! | throwError "axiom traversal exhausted at {name}"
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound do
            throwError "{name} reaches disallowed {ax}"
    unless count > 0 do throwError "module {target} has no declarations"
    logInfo m!"{target}: {count} declarations; axiom ceiling checked"
  let graph := (env.header.moduleNames.zip env.header.moduleData).map
    fun (name, data) => (name, data.imports.map (·.module))
  for target in #[`Effect4.Author, `Effect4.Library, `Effect4.Library.Channel.Ops,
      `Effect4.Library.Stream.Definitions] do
    unless env.header.moduleNames.contains target do
      throwError "missing import boundary root: {target}"
    let closure := ProofGraph.Audit.moduleImportClosure graph target
    if closure.any (fun n => (`Effect4.Laws).isPrefixOf n) then
      throwError "{target} imports the law graph"
  logInfo "core/law import separation checked"
  for source in #["src/Effect4/Laws/Library/Channel/Scope.lean",
      "src/Effect4/Laws/Library/Channel/Protocol.lean",
      "src/Effect4/Laws/Library/Stream/Definitions.lean"] do
    let findings ← ProofGraph.ProofStyle.scanFile env source
    unless findings.isEmpty do
      throwError "new proof-style findings in {source}: {findings.size}"
  logInfo "new law files pass the parsed proof-style check"
