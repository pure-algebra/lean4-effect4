import Effect4.Laws.Api.HostDrive
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

/-- A host meaning regrouped as the host's run, read back. -/
theorem hostRunB_of_meaningUnderB {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (k : Nat) (e : NativeEff) (env : List Val)
    (s : Stores) (st : σ) {ex : ExitV} {s' : Stores} {st' : σ}
    (h : meaningUnderB host k e env s st = some ((some ex, s'), st')) :
    hostRunB host k e env s st = some (some ex, (s', st')) := by
  rw [meaningUnderB_eq_hostRunB] at h
  rcases hm : hostRunB host k e env s st with _ | ⟨o, s₁, st₁⟩
  · rw [hm] at h
    cases h
  · rw [hm] at h
    cases h
    rfl

/-- **H9 at the driver, on loops** (Q9): open a program of the row fragment with loops, evaluate
its root and drive it with a reactor inside the envelope that answers with exits. When the run is
funded, at rest and its root exited, past a budget bound the reactor read as a host runs the
budgeted call tree to the root's exit with the run's stores, and ends at the drive's state.
`runWith_denotes` with H9 on loops in place of H9. It does not establish that the drive
finishes, that its rounds suffice, or that the run is funded. Concept `translation-simulation`,
claim `rows-loop-driver`, role simulation; requirement R6. Consumer: the run interface's hosts
on stream and paging modules. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_denotesB {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.table) (hexits : r.ExitsOnly)
    (hroot : LoopedRows b.program = true) (hfrag : LoopedDataRows b.table b.program = true)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r st id budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b r st id budget rounds).1.exit = some ex) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunB (reactorHost b.table r) k b.program [] Stores.empty st =
        some (some ex, ((Run.runWith b r st id budget rounds).1.machine.state,
          (Run.runWith b r st id budget rounds).2)) := by
  obtain ⟨hreach, hbuilt, hbudget, hA, hhost⟩ :=
    runWith_session b r st id budget rounds henv hexits hfund
  have h := denoteRowsB_eq_session_host (Run.runWith b r st id budget rounds).1 hreach hfund hrest
    hhost
  rw [hbuilt, hbudget] at h
  obtain ⟨lower, hlow⟩ := h hroot hfrag (reactorHost b.table r) st _ hA ex hex
  exact ⟨lower, fun k hk => hostRunB_of_meaningUnderB _ k _ _ _ _ (hlow k hk)⟩

/-- **H9 at the driver on loops, for any reactor behind its rows' types**: `runWith_denotesB` with
the envelope supplied by the guard (`runWith_guarded_denotes` on loops). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_guarded_denotesB {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (hroot : LoopedRows b.program = true)
    (hfrag : LoopedDataRows b.table b.program = true)
    (hfund : funded (Run.runWith b r.guardRows st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r.guardRows st id budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b r.guardRows st id budget rounds).1.exit = some ex) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunB (reactorHost b.table r.guardRows) k b.program [] Stores.empty st =
        some (some ex, ((Run.runWith b r.guardRows st id budget rounds).1.machine.state,
          (Run.runWith b r.guardRows st id budget rounds).2)) :=
  runWith_denotesB b r.guardRows st id budget rounds (guardRows_envelops r b.table)
    (guardRows_exitsOnly r) hroot hfrag hfund hrest ex hex

/-- **H9 at the driver on loops, for any host**: a host of the row signature read as a reactor
behind its rows' types, at a table with distinct keys (`runWith_host_denotes` on loops). The
host behind its rows' types runs the budgeted call tree, past a budget bound, to the root's
exit with the run's stores, and ends at the drive's state. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem runWith_host_denotesB {σ : Type} (b : Api.Built)
    (host : Effects.Comodel (RowSig b.table) σ) (st : σ) (id : String) (budget : Api.Budget)
    (rounds : Nat) (hkeys : (b.table.map rowKey).Nodup) (hroot : LoopedRows b.program = true)
    (hfrag : LoopedDataRows b.table b.program = true)
    (hfund : funded (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1
      = true)
    (hrest : atRest (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1
      = true)
    (ex : ExitV)
    (hex : (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).1.exit =
      some ex) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunB (hostGuard b.table host) k b.program [] Stores.empty st =
        some (some ex, ((Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget
          rounds).1.machine.state,
          (Run.runWith b (Reactor.ofHost b.table host).guardRows st id budget rounds).2)) := by
  rw [← reactorHost_ofHost b.table hkeys host]
  exact runWith_guarded_denotesB b (Reactor.ofHost b.table host) st id budget rounds hroot hfrag
    hfund hrest ex hex

end Effect4.Run
