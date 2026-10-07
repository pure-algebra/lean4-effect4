import Effect4.Laws.Program.Table.Agreement
import Effect4.Laws.Run.Tape

/-!
# Api.SessionRef — a session's reading is the reference machine's replay of its tape (DI-57)

Slice H5 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310). The session
statement follows from the raw statement: `session_eq_ref_of_raw` proves it from any
table-aware agreement of the frame machine with a reference, by the laws of the tape. The raw
agreement with no preloaded answer is a theorem (`run_eq_ref_table_noPreload`, slice H6a), so
`session_eq_ref` is a theorem. Its premise is that the run is recorded and `funded` (the packet,
section 1).
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program

/-- The proposition of `session_eq_ref` (DI-57), over a recorded run: the session's reading and
the reference's replay of the run's own tape. -/
def SessionEqRef : Prop :=
  ∀ (s : Run), Run.Reached s → Run.funded s = true →
    s.inspect.outcome =
        classify (replayR s.built.program s.budget.fuel (Run.tapeOf s) s.budget.compileFuel
          s.built.table) ∧
      obs s.machine =
        obsR (replayR s.built.program s.budget.fuel (Run.tapeOf s) s.budget.compileFuel
          s.built.table).machine

end Effect4.Program.Sched

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Api.HostSession (Phase)
open Effect4.Api.Runner (Command)

/-- Step of `session_eq_ref`: the raw replay of a journal's tape, from the run's machine, is the
raw replay of the empty tape from the machine that the journal leaves. It is `tape_replays` with
the whole replay result in place of its machine: the tape reads every row, so the raw replay
takes every decision. -/
theorem tape_replays_result (s : Run) (rows : List Command) (h : (tapeFrom s rows).2 = []) :
    Run.replayFrom s.built.program s.built.table s.budget.fuel
        ((tapeFrom s rows).1.map (·.decision)) s.machine =
      Run.replayFrom s.built.program s.built.table s.budget.fuel [] (s.play rows).machine := by
  induction rows generalizing s with
  | nil => rfl
  | cons c rest ih =>
    rw [Run.play_cons]
    cases hfront : ((Api.Runner.result s.runner c).phase == Phase.frontier) with
    | true =>
      rw [tapeFrom_frontier s c rest hfront] at h
      cases h
    | false =>
      cases hdec : decisionOf s c (Api.Runner.result s.runner c).phase with
      | none =>
        rw [tapeFrom_skip s c rest hfront hdec] at h ⊢
        have step := ih (s.step c) h
        rw [Run.step_built, Run.step_budget, step_keeps_machine s c hfront hdec] at step
        exact step
      | some decision =>
        cases hreads : readsOn s decision with
        | false =>
          rw [tapeFrom_stop s c rest decision hfront hdec hreads] at h
          cases h
        | true =>
          rw [tapeFrom_take s c rest decision hfront hdec hreads] at h ⊢
          have live : s.machine.stuck.isNone = true ∧
              Run.enoughFor s.built.program s.built.table s.budget.fuel s.machine decision =
                true :=
            Bool.and_eq_true_iff.mp hreads
          have step := ih (s.step c) h
          rw [Run.step_built, Run.step_budget, step_takes_decision s c decision hdec] at step
          rw [List.map_cons,
            Run.replayFrom_cons _ _ _ _ _ _ (Option.isNone_iff_eq_none.mp live.1) live.2]
          exact step

/-- Step of `session_eq_ref`: the session's reading of a machine is the class of the raw replay
of the empty tape from it. -/
theorem inspect_outcome (s : Run) :
    s.inspect.outcome =
      classify (Run.replayFrom s.built.program s.built.table s.budget.fuel [] s.machine) := by
  unfold Run.inspect Api.HostSession.inspect Run.replayFrom Run.machine
  simp only [replayEval]
  generalize s.session.machine = m
  cases hstuck : m.stuck with
  | some why => rfl
  | none =>
    cases hfinished : m.finished with
    | true => simp only [if_true]; rfl
    | false => simp only [Bool.false_eq_true, if_false]; rfl

/-- Step of `session_eq_ref`: the raw replay entry point reports the class of its replay. -/
theorem runOf_outcome (r : NativeReplay) : (Run.runOf r).outcome = classify r := by
  cases r <;> rfl

/-- **The session statement follows from the raw statement** (DI-57). Let a reference agree
with the frame machine at every row table, on every decision tape, at every budget. Then for a
recorded, funded run the session's reading and the reference's replay of the run's own tape
have the same class and the same observation. -/
theorem session_eq_ref_of_raw
    (reference : NativeEff → RowTable → Nat → List Api.Decision → Nat → RReplay)
    (raw : ∀ e table fuel tape compileFuel,
      (Api.replay e fuel tape [] table compileFuel).outcome =
          classify (reference e table fuel tape compileFuel) ∧
        obs (Api.replay e fuel tape [] table compileFuel).machine =
          obsR (reference e table fuel tape compileFuel).machine)
    (s : Run) (recorded : Run.Reached s) (h : funded s = true) :
    s.inspect.outcome =
        classify (reference s.built.program s.built.table s.budget.fuel (tapeOf s)
          s.budget.compileFuel) ∧
      obs s.machine =
        obsR (reference s.built.program s.built.table s.budget.fuel (tapeOf s)
          s.budget.compileFuel).machine := by
  obtain ⟨outcome, observation⟩ :=
    raw s.built.program s.built.table s.budget.fuel (tapeOf s) s.budget.compileFuel
  have read : (tapeFrom (openedOf s) s.journal).2 = [] := List.isEmpty_iff.mp h
  have result := tape_replays_result (openedOf s) s.journal read
  rw [show (openedOf s).play s.journal = s from Run.journal_replays s recorded,
    show (openedOf s).machine = Api.load s.built.program s.budget.compileFuel from
      Run.open_machine s.built s.id s.budget s.profile] at result
  have machine := funded_replays s recorded h
  constructor
  · rw [← outcome, Run.replay_eq, runOf_outcome]
    rw [inspect_outcome]
    exact (congrArg classify result).symm
  · rw [← observation, Run.replay_machine, ← machine]

open Effect4.Program.Denote in
/-- **A session's reading is the reference machine's replay of the run's tape** (DI-57). For a
recorded run that is funded, the session's class and observation are the class and observation
of the reference machine's replay of the run's own tape, at the run's row table and budgets.
Reach: any built program and any journal, under `funded`: no row of the journal is a stopped
row. It does not establish that a run is funded, the session's ledger, reply admission or a
host's conformance. A run with a stopped row is outside it: the control is three calls at a
command budget of 5. It is proved by `session_eq_ref_of_raw` from `run_eq_ref_table_noPreload`
(slice H6a), so it rests on no planned goal. Concept
`translation-simulation`, claim `session-eq-ref`, role simulation; requirement R6. Consumer: the
typed session (decisions row 99), and the meaning of a run's certificate. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem session_eq_ref : SessionEqRef := fun s recorded h =>
  session_eq_ref_of_raw (fun e table fuel tape compileFuel => replayR e fuel tape compileFuel table)
    (fun e table fuel tape compileFuel => run_eq_ref_table_noPreload e table fuel tape compileFuel)
    s recorded h

end Effect4.Run
