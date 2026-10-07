import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Auto.Semantics

/-!
# Program.Table.Agreement — the raw statement at a row table (DI-57)

Slice H5 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310). The frame
machine and the reference machine agree at every row table: the planned goal
`run_eq_ref_table`. `run_eq_ref` (`Laws/Program/RuntimeR.lean`) is its instance at the empty
row table. Its proof is the packet's slice H6.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program

/-- The proposition of `run_eq_ref_table` (the 2026-10-03 note's S1): the frame machine and the
reference agree at every row table, on every decision tape, the preloaded answers included. -/
def RunEqRefTable : Prop :=
  ∀ (e : NativeEff) (table : RowTable) (fuel : Nat) (tape : List Api.Decision)
    (answers : List (Completion Val Err Defect FiberId Ann)) (compileFuel : Nat),
    (Api.replay e fuel tape answers table compileFuel).outcome =
        classify (replayR e fuel tape compileFuel table answers) ∧
      obs (Api.replay e fuel tape answers table compileFuel).machine =
        obsR (replayR e fuel tape compileFuel table answers).machine

/-- **The frame machine and the reference machine agree at every row table.** On every
program, row table, decision tape, list of preloaded answers and pair of budgets, the two
replays end in the same class, and they have the same observation `obs`: every fiber's exit and
the whole stores, the external allocations included. Reach: no premise on the tape, so an answer
that no session admits is in reach. It does not establish reply admission, the typing of a
reply, a host's conformance or the session's ledger. `run_eq_ref` is its instance at the empty
row table with no preloaded answer. Concept `translation-simulation`, claim `run-eq-ref-table`,
role simulation; requirement R6. Consumer: `session_eq_ref`. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal run_eq_ref_table : RunEqRefTable

/-- **The raw statement at every row table, with no preloaded answer** (slice H6a, DI-57). On
every program, row table, decision tape and pair of budgets, from the loads with no preloaded
answer, the frame machine's and the reference machine's replays end in the same class and have
the same observation `obs`. A session loads no preloaded answer, so this is the form that
`session_eq_ref` reads. It is `Machine.Book`'s replay theorem at the two instances at the
table: `stepAgrees` and `hooksAgree_of` hold at every row table under the store invariant
`StoresOk`, whose clause `answers` keeps the registration arm empty and whose clause
`externals` holds at the empty row table alone. It does not establish the case of preloaded
answers (the rest of `run_eq_ref_table`, slice H6b), reply admission, the typing of a reply, a
host's conformance or the session's ledger. A step of the claim `run-eq-ref-table`; consumer:
`session_eq_ref`. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem run_eq_ref_table_noPreload (e : NativeEff) (table : RowTable) (fuel : Nat)
    (tape : List Api.Decision) (compileFuel : Nat) :
    (Api.replay e fuel tape [] table compileFuel).outcome =
        classify (replayR e fuel tape compileFuel table) ∧
      obs (Api.replay e fuel tape [] table compileFuel).machine =
        obsR (replayR e fuel tape compileFuel table).machine := by
  rw [replay_outcome, replay_machine]
  exact replayRel_classify_obs (replay_rel (table := table) e compileFuel fuel tape)

end Effect4.Program.Sched
