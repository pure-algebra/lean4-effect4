import Effect4.Laws.Program.RowProtocol
import ProofGraph.Axioms

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if env.header.moduleNames[idx.toNat]! == `Effect4.Laws.Program.RowProtocol then some name else none
    | none => none).toArray
  unless names.contains ``Effect4.Run.hostAnswered_guardRows do
    throwError "module scan omitted the transfer law"
  let (out, _) := ProofGraph.reachedAxiomsMany env names {}
  for i in [:names.size] do
    let some axioms := out[i]! | throwError "budget exhausted at {names[i]!}"
    unless (axioms.filter fun n => n != ``propext && n != ``Quot.sound).isEmpty do
      throwError "forbidden dependency at {names[i]!}: {axioms}"
    logInfo m!"{names[i]!}: {axioms}"
  logInfo m!"PASS: {names.size} declarations in RowProtocol; exact dependency walk."
