import Effect4.Laws.Program.Typing.Rebase
import ProofGraph.Axioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets := #[`Effect4.Laws.Auto.ExceptMap, `Effect4.Laws.Program.Typing.Rebase]
  let declarations := env.constants.toList.filterMap fun (name, _) =>
    (env.getModuleIdxFor? name).bind fun index =>
      if targets.contains env.header.moduleNames[index.toNat]! then some name else none
  unless !declarations.isEmpty do throwError "audit selected no declarations"
  let (results, _) := ProofGraph.reachedAxiomsMany env declarations.toArray {}
  let mut used : Array Name := #[]
  for declaration in declarations, result in results do
    let some axioms := result | throwError "audit exhausted at {declaration}"
    for axName in axioms do
      unless #[`propext, `Quot.sound].contains axName do
        throwError "unapproved axiom {axName} at {declaration}"
      unless used.contains axName do used := used.push axName
  logInfo m!"audited {declarations.length} declarations across {targets.toList}; reached {used.toList}"
