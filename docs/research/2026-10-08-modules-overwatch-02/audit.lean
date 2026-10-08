import Test.Schema.Modeled
import Test.Program.StepLanguage
import ProofGraph.Audit
import ProofGraph.Axioms
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

run_meta do
  let targets : Array Name := #[`Effect4.Program.TyNormal,
    `Effect4.Laws.Program.TyNormal, `Effect4.Schema.FieldRef,
    `Effect4.Laws.Schema.FieldRef, `Effect4.Modules.Step, `Effect4.Laws.Modules.Step,
    `Test.Program.StepLanguage, `Effect4.Schema.Modeled, `Effect4.Schema.Modeled.Derive,
    `Effect4.Laws.Schema.Modeled, `Test.Schema.Modeled]
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
    let mut choices : Nat := 0
    for i in [:names.size] do
      let name := names[i]!
      if ProofGraph.Audit.moduleOf? env name == some target then
        count := count + 1
        let some axioms := results[i]! | throwError "axiom traversal exhausted at {name}"
        for ax in axioms do
          if ax == ``Classical.choice && target == `Effect4.Schema.Modeled.Derive then
            choices := choices + 1
          else unless ax == ``propext || ax == ``Quot.sound do
            throwError "{name} reaches disallowed {ax}"
    unless count > 0 do throwError "module {target} has no declarations"
    logInfo m!"{target}: {count} declarations; {choices} named meta exceptions; ceiling checked"
  let graph := (env.header.moduleNames.zip env.header.moduleData).map
    fun (name, data) => (name, data.imports.map (·.module))
  for target in #[`Effect4.Schema.Modeled, `Effect4.Schema.Modeled.Derive,
      `Effect4.Program.TyNormal, `Effect4.Schema.FieldRef, `Effect4.Modules.Step] do
    let closure := ProofGraph.Audit.moduleImportClosure graph target
    if closure.any (fun n => (`Effect4.Laws).isPrefixOf n) then
      throwError "{target} imports the law graph"
  logInfo "core/law import separation checked"
