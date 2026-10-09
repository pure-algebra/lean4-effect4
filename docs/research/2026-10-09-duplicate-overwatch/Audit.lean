import Effect4.Author
import Effect4.Laws.Library.Semaphore.Data
import Effect4.Laws.Library.Pool.Ops
import Effect4.Laws.Codegen.PrintTyped
import Test.Program.RegistrationYield
import ProofGraph.Audit
import ProofGraph.Axioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Effect4.Laws.Library.Semaphore.Data, `Effect4.Laws.Library.Pool.Ops,
    `Effect4.Laws.Codegen.PrintTyped, `Test.Program.RegistrationYield]
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some m := ProofGraph.Audit.moduleOf? env name then
      if modules.contains m then roots := roots.push name
  let (results, _) := ProofGraph.reachedAxiomsMany env roots {}
  let allowed := #[`propext, `Quot.sound]
  let mut lines : List String := []
  for (name, result) in roots.zip results do
    let some axioms := result | throwError "Audit exhausted at {name}"
    for ax in axioms do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} reached by {name}"
    lines := s!"{name}\t{axioms.toList}" :: lines
  liftIO <| IO.FS.writeFile "axioms.tsv" (String.intercalate "\n" lines.reverse ++ "\n")
  for m in modules do
    let count : Nat := roots.foldl (fun n name => if ProofGraph.Audit.moduleOf? env name == some m then n + 1 else n) 0
    logInfo m!"{m}: {count} declarations within [propext, Quot.sound]"
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (m, d) =>
    (m, d.imports.map (·.module))
  let closure := ProofGraph.Audit.moduleImportClosure graph `Effect4.Author
  for m in closure do
    if (`Effect4.Laws).isPrefixOf m then throwError "Author imports Laws: {m}"
  liftIO <| IO.FS.writeFile "imported-project-modules.txt"
    (String.intercalate "\n" (env.header.moduleNames.toList.filterMap fun n =>
      if (`Effect4).isPrefixOf n || (`Test).isPrefixOf n || (`ProofGraph).isPrefixOf n then
        some n.toString else none) ++ "\n")
  logInfo m!"PASS: {roots.size} declarations checked; Author imports no Laws module."
