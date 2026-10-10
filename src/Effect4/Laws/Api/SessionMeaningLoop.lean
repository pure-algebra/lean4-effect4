import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Agreement.HostedLoop

/-!
# Api.SessionMeaningLoop — H8 and H9 on loops

Slice L1 of `docs/research/2026-10-10-host-meaning-widening/README.md` (§1.3, §1.4, §5.1 Q7 and
Q8). `denoteRows_eq_session` and `denoteRows_eq_session_host` (`Laws/Api/SessionMeaning.lean`)
hold on `StraightRows`. Here the same session prefix (`session_settled`) closes with the loop
closing step (`meaning_settledB_tape`, `hostRunB_exits`, `Laws/Program/Agreement/HostedLoop.lean`),
on programs of `LoopedRows` that the row fragment with loops admits (`LoopedDataRows`).

The bound on the budget is existential: a loop's count depends on the replies and the branches.
No global compile-depth premise enters. A finite budget cut is never a typed failure and never a
divergence claim. H8's observation is coarse: an unfinished run is `none`, budget cut or wait
alike (the frontier claim Q4 separates them). H9 keeps completion as a premise: past answers do
not fix an unanswered next call.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-- The proposition of `h8_loopedRows`: H8 on the row fragment with loops, past a budget bound. -/
def H8LoopedRows : Prop :=
  ∀ (s : Run), Run.Reached s → funded s = true → atRest s = true → hostDriven s = true →
    LoopedRows s.built.program = true → LoopedDataRows s.built.table s.built.program = true →
    ∃ lower, ∀ k, lower ≤ k →
      coarseRowsB s.built.table k s.built.program [] Stores.empty (appliedExits s) =
        s.exit.map fun ex => ((ex, s.machine.state), [])

/-- The proposition of `denoteRowsB_eq_session_host`: H9 on the row fragment with loops, for a
finished run, past a budget bound. -/
def H9LoopedRows : Prop :=
  ∀ (s : Run), Run.Reached s → funded s = true → atRest s = true → hostDriven s = true →
    LoopedRows s.built.program = true → LoopedDataRows s.built.table s.built.program = true →
    ∀ {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ),
      HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
        (Api.load s.built.program s.budget.compileFuel) st st' →
      ∀ ex, s.exit = some ex → ∃ lower, ∀ k, lower ≤ k →
        meaningUnderB host k s.built.program [] Stores.empty st =
          some ((some ex, s.machine.state), st')

/-- **H8 on loops** (Q7): for a recorded run of a program of the row fragment with loops that is
funded, at rest and driven by a host, past a budget bound the coarse observation of the budgeted
meaning under the run's reply tape is the root's exit with the stores, the tape read to its end;
where the root has no exit it is `none`. Concept `translation-simulation`, claim
`rows-loop-session`, role simulation; requirement R6. Consumers: the paged data-row client and the
driver theorem on loops. It establishes no scope, external handle allocation, interruption, fork,
progress or target claim, and no waiting position's stores or request. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem h8_loopedRows : H8LoopedRows := by
  intro s hreach hfund hrest hhost hroot hfrag
  obtain ⟨p, hS, harmed, hL, hexit⟩ := session_settled s hreach hfund hrest hhost hroot
    (tapeHost s.built.table) _ _ (session_tapeAnswered s hfund hhost)
  rw [hexit]
  exact meaning_settledB_tape s.built.program hfrag s.budget.compileFuel (appliedExits s) hS harmed hL

/-- **H9 on loops** (Q8): for a finished recorded run of the same fragment, under any host whose
answers are the run's (`HostAnswered`), past a budget bound the budgeted meaning under the host is
the root's exit with the stores, and the host ends where the answers left it. H8 on loops at a
finished run is its instance at the reply host. Concept `translation-simulation`, claim
`rows-loop-host`, role simulation; requirement R6. Consumer: the driver theorem on loops (Q9). It
does not establish that a host's drive finishes, nor anything of a run that stopped at a call. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem denoteRowsB_eq_session_host : H9LoopedRows := by
  intro s hreach hfund hrest hhost hroot hfrag σ host st st' hA ex hex
  obtain ⟨p, hS, -, hL, hexit⟩ := session_settled s hreach hfund hrest hhost hroot host st st' hA
  rcases hS with ⟨cur, K, i, s', n, tr, t, hm, -, -⟩ | ⟨cur, K, i, s', n, tr, t, hm, -, -⟩ |
    ⟨ex', fr, s', n, tr, nt, hm, rfl, -⟩
  · rw [hexit, hm, Myield_fiber?] at hex
    cases hex
  · rw [hexit, hm, Mcall_fiber?] at hex
    cases hex
  · rw [hexit, hm, Mexit_exit] at hex
    cases hex
    obtain ⟨lower, hlow⟩ := hostRunB_exits host s.built.program hfrag s.budget.compileFuel st st' hL
    refine ⟨lower, fun k hk => ?_⟩
    rw [meaningUnderB_eq_hostRunB, hlow k hk, hm]
    rfl

end Effect4.Run
