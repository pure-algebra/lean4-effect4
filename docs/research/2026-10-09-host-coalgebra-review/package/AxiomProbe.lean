import Effects.Coalgebra
import ProofGraph.Axioms

open Lean Elab Command
set_option maxHeartbeats 0

-- A narrow declaration-list check, not the package or Effect4 whole-library gate.
run_cmd do
  let env ← getEnv
  let names := #[
    ``Effects.Step.map_id, ``Effects.Step.map_comp,
    ``Effects.unfold_eq_of_bisim, ``Effects.unfold_approx_of_sim,
    ``Effects.Program.unfold_system,
    ``Effects.Program.run_of_sim_program,
    ``Effects.System.run_eq_of_bisim, ``Effects.System.run_mono,
    ``Effects.System.run_peel,
    ``Effects.Comodel.run_route_inl, ``Effects.Comodel.run_route_inr,
    ``Effects.Comodel.run_share_inl, ``Effects.Comodel.run_share_inr,
    ``Effects.Comodel.run_rename, ``Effects.Comodel.run_through,
    ``Effects.Comodel.run_record_replies,
    ``Effects.Comodel.handler_ofHandler, ``Effects.Comodel.ofHandler_handler,
    ``Effects.Comodel.run_ofHandler,
    ``Effects.Comodel.guard_meets, ``Effects.Comodel.guard_of_meets]
  let (out, _) := ProofGraph.reachedAxiomsMany env names {}
  for i in [:names.size] do
    let some axioms := out[i]! | throwError "budget exhausted at {names[i]!}"
    let forbidden := axioms.filter fun n => n != ``propext && n != ``Quot.sound
    unless forbidden.isEmpty do
      throwError "{names[i]!}: forbidden {forbidden}"
    logInfo m!"{names[i]!}: {axioms}"
  logInfo m!"PASS: {names.size} selected declarations; exact dependency walk."
