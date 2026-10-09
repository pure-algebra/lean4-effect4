import Effect4
import Effect4.Author
import Effect4.Laws.Author
import ProofGraph.Audit
import ProofGraph.Axioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let graph := env.header.moduleNames.zip env.header.moduleData |>.map fun (n, d) =>
    (n, d.imports.map (·.module))
  for root in #[`Effect4, `Effect4.Author] do
    let closure := ProofGraph.Audit.moduleImportClosure graph root
    for m in closure do
      if (`Effect4.Laws).isPrefixOf m then throwError "core entry reaches law: {root} -> {m}"
  let names := #[`Effect4.Program.EditSession.reached_view,
    `Effect4.Program.EditSession.feed_undo, `Effect4.Program.EditSession.feed_repaint,
    `Effect4.Store.Canonical.ofJson_exact]
  let (results, _) := ProofGraph.reachedAxiomsMany env names {}
  let allowed := #[`propext, `Quot.sound]
  for (name, result) in names.zip results do
    let some axioms := result | throwError "audit exhausted: {name}"
    for ax in axioms do
      unless allowed.contains ax do throwError "unexpected axiom: {name} -> {ax}"
    logInfo m!"{name}: {axioms}"
  logInfo "PASS: core and author entries import no Laws module; selected edit and canonical reader laws stay at the allowed ceiling"
