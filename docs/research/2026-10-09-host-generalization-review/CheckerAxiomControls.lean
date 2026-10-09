import Effect4.Laws.Api.SessionMeaning
import ProofGraph.Axioms

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let names := #[``Effect4.Program.Denote.hostRun_eq_meaningUnder,
    ``Effect4.Program.Denote.runRowsH_bind,
    ``Effect4.Program.Denote.hostRun_call,
    ``Effect4.Program.Agreement.localRunC_compile,
    ``Effect4.Program.Agreement.drive_seg,
    ``Effect4.Program.Agreement.holds_answer,
    ``Effect4.Program.Agreement.meaning_settled,
    ``Effect4.Program.Agreement.meaning_settled_tape,
    ``Effect4.Run.preflight_row,
    ``Effect4.Run.tapeFrom_answered,
    ``Effect4.Run.denoteRows_eq_session,
    ``Effect4.Program.Agreement.Holds.hostAnswer_eq,
    ``Effect4.Run.tape_holds_host,
    ``Effect4.Run.answered_hostAnswered,
    ``Effect4.Run.denoteRows_eq_session_host,
    ``Effect4.Run.hostAnsweredCheck_sound]
  let (out, _) := ProofGraph.reachedAxiomsMany env names {}
  for i in [:names.size] do
    let some axioms := out[i]! | throwError "budget exhausted at {names[i]!}"
    unless (axioms.filter fun n => n != ``propext && n != ``Quot.sound).isEmpty do
      throwError "forbidden dependency at {names[i]!}: {axioms}"
    logInfo m!"{names[i]!}: {axioms}"
  logInfo m!"PASS: {names.size} changed laws; exact dependency walk."
