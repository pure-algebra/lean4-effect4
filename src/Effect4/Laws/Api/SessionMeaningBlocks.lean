import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Agreement.HostedBlocks
import Effect4.Laws.Auto.Semantics

/-!
# Completed recorded runs and block meaning

Concept: translation-simulation. Claim: rows-block-host, R6, serving R10.
Consumers: validated block claims. Reach: reached, funded, settled and completed BlockRows runs.
The host answers match the recorded tape. This statement establishes no progress or target claim.
-/

set_option autoImplicit false
namespace Effect4.Run
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-- The completed-session observation for `rows-block-host`.
Reach: reached, funded, settled, host-driven block runs and matching host answers.
The initial context and stores are empty. No termination or progress follows. -/
def H9Blocks : Prop :=
  ∀ (s : Run), Run.Reached s → funded s = true → atRest s = true → hostDriven s = true →
    BlockRows s.built.table s.built.program = true →
    ∀ {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ),
      HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
        (Api.load s.built.program s.budget.compileFuel) st st' →
      ∀ ex, s.exit = some ex → ∃ lower, ∀ k, lower ≤ k →
        runRowsH host (denoteBlockB s.built.table (bodiesOf s.built.program) k []
          s.built.program emptyCtx []) Stores.empty st =
            some (some ex, (s.machine.state, st'))

/-- Simulation claim `rows-block-host`, R6, serving R10.
Consumers: `conforms_sat_blocks` and `agrees_hostRun_blocks`.
Reach: exactly `H9Blocks`. It proves no runtime-target agreement, progress, or funding. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem h9_blocks : H9Blocks := by
  intro s hreach hfund hrest hhost hfrag σ host st st' hA ex hex
  obtain ⟨p, hS, -, hL, hexit⟩ := session_settled s hreach hfund hrest hhost
    (PlainHooks.of_blockRows hfrag) host st st' hA
  rcases hS with ⟨cur, K, i, s', n, tr, t, ctx, hm, -, -⟩ |
    ⟨cur, K, i, s', n, tr, t, ctx, hm, -, -⟩ | ⟨ex', fr, s', n, tr, nt, ctx, hm, rfl, -⟩
  · rw [hexit, hm, Myield_fiber?] at hex
    cases hex
  · rw [hexit, hm, Mcall_fiber?] at hex
    cases hex
  · rw [hexit, hm, Mexit_exit] at hex
    cases hex
    obtain ⟨lower, hlow⟩ := hostRunBlockB_exits host s.built.program hfrag
      s.budget.compileFuel st st' hL
    refine ⟨lower, fun k hk => ?_⟩
    change hostRunBlockB host (bodiesOf s.built.program) k [] s.built.program emptyCtx []
      Stores.empty st = _
    rw [hlow k hk, hm]
    rfl
end Effect4.Run
