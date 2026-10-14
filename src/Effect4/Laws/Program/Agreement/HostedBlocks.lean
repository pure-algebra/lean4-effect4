import Effect4.Laws.Program.Agreement.Blocks
import Effect4.Laws.Program.Agreement.Hosted
import Effect4.Laws.Auto.Semantics

/-!
# Completed local runs and block meaning

Concept: translation-simulation. Claim: rows-block-host, R6; stability also serves R10.
Consumers: h9_blocks and validated block claims. Reach: completed BlockRows runs at empty context.
The proofs retain their finished-run premises and establish no progress.
-/

set_option autoImplicit false
namespace Effect4.Program.Agreement
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
variable {table : RowTable}

/-- Step of block-handler-monotone (R10), consumed by `hostRunBlockB_exits`.
An empty parameter list yields a monotone budget chain at every context.
A finished host observation persists; no cut implies progress. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem hostRunBlockB_stable {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (bodies : List NativeEff) {k k' : Nat} (hk : k ≤ k') (e : NativeEff)
    (ctx : Ctx) (env : List Val) (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ)
    (h : hostRunBlockB host bodies k [] e ctx env s st = some (some ex, out)) :
    hostRunBlockB host bodies k' [] e ctx env s st = some (some ex, out) := by
  induction hk with
  | refl => exact h
  | @step j hj ih =>
    have hparams : ([] : List (ParamTreeB table)).length = ([] : List (ParamTreeB table)).length ∧
        ∀ (n : Nat) (f g : ParamTreeB table), ([] : List (ParamTreeB table))[n]? = some f →
          ([] : List (ParamTreeB table))[n]? = some g → ∀ ctx w,
            Effects.Program.Approx (f ctx w) (g ctx w) := by
      refine ⟨rfl, ?_⟩
      intro n f g hf
      cases hf
    exact Effects.Comodel.run_approx (rowsHost host)
      (denoteBlockB_approx table bodies j [] [] hparams e ctx env) ih

/-- Step of `rows-block-host`, R6. Consumer: `hostRunBlockB_exits`.
Reach: a local run from the block root that already exits.
It supplies one finished meaning budget, not termination or scheduler progress. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem localRunC_to_blockB {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hfrag : BlockRows table root = true) (cf : Nat) (R : σ)
    {c : Nat} {ex : ExitV} {s' : Stores} {r' : σ}
    (h : localRunC host root c (fiberOf (compile root cf) []) Stores.empty R =
      some (.exit ex s' r')) :
    ∃ k, hostRunBlockB host (bodiesOf root) k [] root emptyCtx [] Stores.empty R =
      some (some ex, (s', r')) := by
  refine ⟨c, ?_⟩
  have hR : RunsToDO host root [] true c (fiberOf (compile root cf) []) Stores.empty R
      (runRowsO host (denoteBlockB table (bodiesOf root) c [] root emptyCtx []) Stores.empty R) :=
    compilesBlk_root host root hfrag c (rootPoint cf) [] true Stores.empty R rfl rfl
  have hnodiv : ¬ Diverges host root (fiberOf (compile root cf) []) Stores.empty R := by
    rintro ⟨d, fr', s₁, r₁, hd, hfront⟩
    have h₁ := localRunC_mono c d _ _ _ h
    rw [hd c, localRunC_frontier _ s₁ r₁ hfront] at h₁
    cases h₁
  unfold hostRunBlockB
  rw [runRowsH_eq_project]
  rcases hm : runRowsO host (denoteBlockB table (bodiesOf root) c [] root emptyCtx [])
      Stores.empty R with ⟨_ | ex₂, s₂, r₂⟩ | ⟨row, request, s₂, r₂⟩
  · rw [hm] at hR
    rcases hR with ⟨d, fr', s₁, r₁, hcd, hd⟩ | hdiv
    · have h₁ := localRunC_mono c (d - c) _ _ _ h
      rw [Nat.add_sub_cancel' hcd, ← Nat.zero_add d, hd 0] at h₁
      cases h₁
    · exact absurd hdiv hnodiv
  · rw [hm] at hR
    rcases hR with ⟨d, hd⟩ | hdiv
    · have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
      cases localRunC_agree h he
      rfl
    · exact absurd hdiv hnodiv
  · rw [hm] at hR
    rcases hR with ⟨d, fr', hd, hc, hcall, ha⟩ | hdiv
    · have hw := (hd 1).trans (localRunC_waits hc ha s₂ 0)
      cases localRunC_agree h hw
    · exact absurd hdiv hnodiv

/-- Step of `rows-block-host`, R6. Consumer: `h9_blocks`.
Reach: a local run already leading to a completed root exit.
Monotonicity retains that exit past a meaning-budget bound. No progress follows. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem hostRunBlockB_exits {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hfrag : BlockRows table root = true) (cf : Nat) (R st : σ)
    {ex : ExitV} {s : Stores}
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R (.done ex s) st) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunBlockB host (bodiesOf root) k [] root emptyCtx [] Stores.empty R =
        some (some ex, (s, st)) := by
  obtain ⟨c, hrun⟩ := hL
  obtain ⟨k₀, hk₀⟩ := localRunC_to_blockB host root hfrag cf R hrun
  exact ⟨k₀, fun k hk => hostRunBlockB_stable host (bodiesOf root) hk root emptyCtx []
    Stores.empty R ex (s, st) hk₀⟩
end Effect4.Program.Agreement
