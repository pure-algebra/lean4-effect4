import Effect4.Laws.Program.Agreement.Segment

/-!
# Receipt-conditioned context segments

Concept: translation-simulation. Claim: rows-block-host, requirement R6.
The consumer is the hosted decision proof in Agreement/Hosted.lean.
The fragment admits plain hooks, one root and quiet stores at every context.
An actual command receipt supplies completion. These laws supply no progress bound.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-- A completed segment's three forms retain its actual context and observation.
Only the completed exit omits context from its local observation. -/
def ContextSegOwes (root : NativeEff) (table : RowTable) (fr : NFiber) (s : Stores)
    (ctx : Ctx) (result : Api.Machine) : Prop :=
  (∃ ex s' fr' k tr nt ctx', result = Mexit root ex fr' s' k tr nt ctx' ∧ Quiet s' ∧
    (∀ {σ : Type} (host : Effects.Comodel (RowSig table) σ) (r : σ),
      ∃ c, localRunC host root c fr s r ctx = some (.exit ex s' r))) ∨
  (∃ cur K i s' k tr nt ctx', result = Mcall (fiberOf cur K i) s' k tr nt ctx' ∧
    IsCall cur = true ∧ PlainStack K ∧ Quiet s' ∧
    ∃ c, ReachesQ (table := table) root c fr s (fiberOf cur K i) s' ctx ctx') ∨
  (∃ cur K i s' k tr nt ctx', result = Myield (fiberOf cur K i) s' k tr nt ctx' ∧
    PlainCode cur = true ∧ PlainStack K ∧ Quiet s' ∧
    ∃ c, ReachesQ (table := table) root c fr s (fiberOf cur K i) s' ctx ctx')

/-! These helpers serve `drive_seg_receipt`, rows-block-host/R6.
They transport actual finite receipts and exact local observations.
They provide no command bound or scheduler progress. -/

@[semantics "translation-simulation" (requirement := R6)]
theorem drive_receipt_stable (root : NativeEff) (fuel : Nat) (m : Api.Machine)
    (cmds : List NCmd)
    (h : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel m cmds) = true) (k : Nat) :
    driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + k) m cmds =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds := by
  simp only [settled, Bool.or_eq_true] at h
  rcases h with h | h
  · have he : (driveState (evaluator := evaluatorFor root table)
        (interpOf root table) fuel m cmds).2 = [] := by
      cases hc : (driveState (evaluator := evaluatorFor root table)
          (interpOf root table) fuel m cmds).2 with
      | nil => rfl
      | cons head tail => simp only [hc, List.isEmpty_cons, Bool.false_eq_true] at h
    rw [driveState_done_add (evaluator := evaluatorFor root table) _ _ _ _ he]
    exact Prod.ext rfl he.symm
  · rw [driveState_add (evaluator := evaluatorFor root table),
      driveState_stuck (evaluator := evaluatorFor root table) _ _ _ _ h]

@[semantics "translation-simulation" (requirement := R6)]
theorem drive_receipt_prefix (root : NativeEff) (fuel a : Nat) (m m' : Api.Machine)
    (cmds cmds' : List NCmd)
    (h : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel m cmds) = true)
    (hn : settled (m', cmds') = false)
    (hp : ∀ n, driveState (evaluator := evaluatorFor root table)
      (interpOf root table) (n + a) m cmds =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n m' cmds') :
    ∃ rest, fuel = rest + a ∧
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds =
        driveState (evaluator := evaluatorFor root table) (interpOf root table) rest m' cmds' := by
  have hle : a ≤ fuel := by
    by_contra hx
    have hs := drive_receipt_stable root fuel m cmds h (a - fuel)
    rw [show fuel + (a - fuel) = a by omega] at hs
    have hz := hp 0
    simp only [Nat.zero_add, driveState_zero] at hz
    have he : settled (m', cmds') = true := by rw [← hz, hs]; exact h
    rw [hn] at he
    cases he
  refine ⟨fuel - a, by omega, ?_⟩
  have hx := hp (fuel - a)
  rw [Nat.sub_add_cancel hle] at hx
  exact hx

@[semantics "translation-simulation" (requirement := R6)]
theorem drive_receipt_result (root : NativeEff) (fuel a : Nat) (m result : Api.Machine)
    (cmds : List NCmd)
    (h : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel m cmds) = true)
    (hp : ∀ n, driveState (evaluator := evaluatorFor root table)
      (interpOf root table) (n + a) m cmds = (result, [])) :
    driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds =
      (result, []) := by
  have hs := drive_receipt_stable root fuel m cmds h a
  rw [hp fuel] at hs
  exact hs.symm

@[semantics "translation-simulation" (requirement := R6)]
theorem ContextSegOwes.prepend {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    {ctx ctx' : Ctx} {result : Api.Machine} {c : Nat}
    (hr : ReachesQ (table := table) root c fr s fr' s' ctx ctx')
    (ho : ContextSegOwes root table fr' s' ctx' result) :
    ContextSegOwes root table fr s ctx result := by
  rcases ho with ⟨ex, s'', fr'', k, tr, nt, ctx'', heq, hq, he⟩ |
    ⟨cur, K, i, s'', k, tr, nt, ctx'', heq, hc, hK, hq, a, ha⟩ |
    ⟨cur, K, i, s'', k, tr, nt, ctx'', heq, hpl, hK, hq, a, ha⟩
  · refine Or.inl ⟨ex, s'', fr'', k, tr, nt, ctx'', heq, hq, ?_⟩
    intro σ host r
    obtain ⟨n, hn⟩ := he host r
    exact ⟨n + c, (hr host r n).trans hn⟩
  · exact Or.inr (Or.inl ⟨cur, K, i, s'', k, tr, nt, ctx'', heq, hc, hK, hq,
      c + a, hr.trans ha⟩)
  · exact Or.inr (Or.inr ⟨cur, K, i, s'', k, tr, nt, ctx'', heq, hpl, hK, hq,
      c + a, hr.trans ha⟩)

@[semantics "translation-simulation" (requirement := R6)]
theorem context_run_finish {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {fr : NFiber} {s s' : Stores} {ctx ctx' : Ctx} {ex : ExitV}
    (h : contextStep root fr s ctx = (.finished ex s', ctx'))
    (hc : IsCall fr.current = false) (r : σ) :
    localRunC host root 1 fr s r ctx = some (.exit ex s' r) := by
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, h]

@[semantics "translation-simulation" (requirement := R6)]
theorem context_receipt_finish (root : NativeEff) (fuel : Nat) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (ctx : Ctx) (d : Bool)
    (ex : ExitV) (ctx' : Ctx) (fr' : NFiber) (k' : Nat) (tr' : NTrace)
    (hq : Quiet s) (hstep : contextStep root (fiberOf cur K i) s ctx = (.finished ex s, ctx'))
    (hc : IsCall cur = false)
    (hdrv : ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      (n + 1) (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (M fr' s k' tr' nt ctx') [Cmd.finish Api.root ex, Cmd.drainDue])
    (hreceipt : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel (M (fiberOf cur K i) s k tr nt ctx)
      [cmdOf d, Cmd.drainDue]) = true) :
    ∃ result, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] = (result, []) ∧
      ContextSegOwes root table (fiberOf cur K i) s ctx result := by
  obtain ⟨tr'', hfin⟩ := drive_finish_M_context (table := table) root ctx' ex fr' s k' tr' nt [Cmd.drainDue]
  refine ⟨Mexit root ex fr' s k' tr'' nt ctx', ?_, ?_⟩
  · apply drive_receipt_result root fuel 4 _ _ _ hreceipt
    intro n
    rw [show n + 4 = n + 1 + 1 + 1 + 1 by omega, hdrv, hfin,
      drive_drainDue root _ _ _ rfl hq, drive_drainDue root _ _ _ rfl hq, drive_nil]
  · exact Or.inl ⟨ex, s, fr', k', tr'', nt, ctx', rfl, hq,
      fun host r => ⟨1, context_run_finish hstep hc r⟩⟩

/-- The actual receipt closes a segment. It admits exhausted commands or a stuck machine.
Plain hooks rule out the stuck-machine alternative in the conclusion.
Consumer: hosted evaluate, flush and answer; rows-block-host/R6. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem drive_seg_receipt (root : NativeEff) (hroot : PlainHooks root)
    (fuel : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) (ctx : Ctx) (d : Bool)
    (hpl : PlainCode cur = true) (hK : PlainStack K) (hq : Quiet s)
    (hd : d = true → (∀ t, cur ≠ Prim.sync t) ∧ IsCall cur = false)
    (hreceipt : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel (M (fiberOf cur K i) s k tr nt ctx)
      [cmdOf d, Cmd.drainDue]) = true) :
    ∃ result, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] = (result, []) ∧
      ContextSegOwes root table (fiberOf cur K i) s ctx result
 := by
  induction fuel using Nat.strongRecOn generalizing cur K i s k tr nt ctx d with
  | ind fuel ih =>
    have recurse (a : Nat) (ha : 0 < a) (cur₁ : NCode) (K₁ : List NCode) (i₁ : Bool)
        (s₁ : Stores) (k₁ : Nat) (tr₁ : NTrace) (ctx₁ : Ctx) (d₁ : Bool)
        (hpl₁ : PlainCode cur₁ = true) (hK₁ : PlainStack K₁) (hq₁ : Quiet s₁)
        (hd₁ : d₁ = true → (∀ t, cur₁ ≠ Prim.sync t) ∧ IsCall cur₁ = false)
        (hr : ReachesQ (table := table) root 1 (fiberOf cur K i) s
          (fiberOf cur₁ K₁ i₁) s₁ ctx ctx₁)
        (hdrive : ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table)
          (n + a) (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] =
          driveState (evaluator := evaluatorFor root table) (interpOf root table) n
            (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt ctx₁) [cmdOf d₁, Cmd.drainDue]) :
        ∃ result, driveState (evaluator := evaluatorFor root table) (interpOf root table)
          fuel (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] = (result, []) ∧
          ContextSegOwes root table (fiberOf cur K i) s ctx result := by
      obtain ⟨rest, hfuel, hnext⟩ := drive_receipt_prefix root fuel a _ _ _ _ hreceipt rfl hdrive
      have hreceipt₁ : settled (driveState (evaluator := evaluatorFor root table)
          (interpOf root table) rest (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt ctx₁)
          [cmdOf d₁, Cmd.drainDue]) = true := by rw [← hnext]; exact hreceipt
      obtain ⟨result, heq, ho⟩ := ih rest (by omega) cur₁ K₁ i₁ s₁ k₁ tr₁ nt ctx₁ d₁
        hpl₁ hK₁ hq₁ hd₁ hreceipt₁
      exact ⟨result, hnext.trans heq, ho.prepend hr⟩
    have advance (hns : ∀ t, cur ≠ Prim.sync t) (hnc : IsCall cur = false)
        (hk : d = false → (stores.budgetOf ctx).2 = true ∨ k + 1 < (stores.budgetOf ctx).1) :
        ∃ result, driveState (evaluator := evaluatorFor root table) (interpOf root table)
          fuel (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] = (result, []) ∧
          ContextSegOwes root table (fiberOf cur K i) s ctx result := by
      rcases hstep : contextStep root (fiberOf cur K i) s ctx with ⟨step, ctx'⟩
      cases step with
      | running fr' s' =>
        have hs := contextStep_stores hns hstep
        subst s'
        obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
          contextStep_plain hroot cur K i s s ctx ctx' fr' hpl hK hstep
        have hreach : ReachesQ (table := table) root 1 (fiberOf cur K i) s
            (fiberOf cur₁ K₁ i₁) s ctx ctx' := ReachesQ.contextStep hstep hnc
        obtain ⟨k₁, tr₁, hdrv⟩ : ∃ k₁ tr₁, ∀ n,
            driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
              (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] =
            driveState (evaluator := evaluatorFor root table) (interpOf root table) n
              (M (fiberOf cur₁ K₁ i₁) s k₁ tr₁ nt ctx') [cmdOf false, Cmd.drainDue] := by
          cases d with
          | false =>
            obtain ⟨tr₁, hdrv⟩ := drive_loop_running_context (table := table) root ctx hroot ctx' cur K i s k tr nt
              [Cmd.drainDue] cur₁ K₁ i₁ hpl hK hns hnc (hk rfl) hstep
            exact ⟨k + 1, tr₁, hdrv⟩
          | true =>
            obtain ⟨tr₁, hdrv⟩ := drive_deliver_running_context (table := table) root ctx hroot ctx' cur K i s k tr nt
              [Cmd.drainDue] cur₁ K₁ i₁ hpl hK hns hnc hstep
            exact ⟨k, tr₁, hdrv⟩
        exact recurse 1 (by decide) cur₁ K₁ i₁ s k₁ tr₁ ctx' false hpl₁ hK₁ hq
          (fun h => by cases h) hreach hdrv
      | finished ex s' =>
        have hs := (contextStep_finished_stores hstep).1
        subst s'
        obtain ⟨k₁, tr₁, hdrv⟩ : ∃ k₁ tr₁, ∀ n,
            driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
              (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] =
            driveState (evaluator := evaluatorFor root table) (interpOf root table) n
              (M (frameExitState (fiberOf cur K i)) s k₁ tr₁ nt ctx')
              [Cmd.finish Api.root ex, Cmd.drainDue] := by
          cases d with
          | false =>
            obtain ⟨tr₁, hdrv⟩ := drive_loop_finish_context (table := table) root ctx hroot ctx' cur K i s k tr nt
              [Cmd.drainDue] ex hpl hK hns (hk rfl) hstep
            exact ⟨k + 1, tr₁, hdrv⟩
          | true =>
            obtain ⟨tr₁, hdrv⟩ := drive_deliver_finish_context (table := table) root ctx hroot ctx' cur K i s k tr nt
              [Cmd.drainDue] ex hpl hK hns hstep
            exact ⟨k, tr₁, hdrv⟩
        exact context_receipt_finish root fuel cur K i s k tr nt ctx d ex ctx'
          (frameExitState (fiberOf cur K i)) k₁ tr₁ hq hstep hnc hdrv hreceipt
    cases d with
    | true => exact advance (hd rfl).1 (hd rfl).2 (fun h => by cases h)
    | false =>
      by_cases hk : (stores.budgetOf ctx).2 = true ∨ k + 1 < (stores.budgetOf ctx).1
      · cases hc : IsCall cur with
        | true =>
          obtain ⟨tr₁, hdrv⟩ := drive_loop_call_context (table := table) root cur K i s k tr nt [Cmd.drainDue] ctx hc hk
          refine ⟨Mcall (fiberOf cur K i) s (k + 1) tr₁ nt ctx, ?_, ?_⟩
          · apply drive_receipt_result root fuel 2 _ _ _ hreceipt
            intro n
            simp only [cmdOf]
            rw [show n + 2 = n + 1 + 1 by omega, hdrv,
              drive_drainDue root _ _ _ rfl hq, drive_nil]
          · exact Or.inr (Or.inl ⟨cur, K, i, s, k + 1, tr₁, nt, ctx, rfl, hc, hK, hq,
              0, ReachesQ.refl root _ _ ctx⟩)
        | false =>
          cases hsync : isSync cur with
          | false => exact advance (not_sync_of_isSync_false hsync) hc (fun _ => hk)
          | true =>
            obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsync
            cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
            · rename_i p
              obtain ⟨tr₁, hdrv⟩ := drive_loop_sync_pure_context (table := table) root ctx p K i s k tr nt [Cmd.drainDue] hk
              exact recurse 1 (by decide) _ K i s (k + 1) tr₁ ctx true rfl hK hq
                (fun _ => ⟨(fun _ h => by cases h), rfl⟩)
                (ReachesQ.step (step_sync_pure root p K i s) rfl (fun _ h => by cases h)) hdrv
            · rename_i o
              cases hso : syncOpStep o s with
              | none =>
                obtain ⟨tr₁, hdrv⟩ := drive_loop_sync_op_none_context (table := table) root ctx o K i s k tr nt [Cmd.drainDue] hk hso
                have hstep : localStep root (fiberOf (Prim.sync (.op o)) K i) s =
                    .running (fiberOf (Prim.success Val.unit) K i) s := by rw [step_sync_op, hso]
                exact recurse 1 (by decide) _ K i s (k + 1) tr₁ ctx true rfl hK hq
                  (fun _ => ⟨(fun _ h => by cases h), rfl⟩)
                  (ReachesQ.step hstep rfl (fun _ h => by cases h)) hdrv
              | some answer =>
                rcases answer with ⟨s₁, v⟩
                have hq₁ := syncOpStep_quiet hso hq
                obtain ⟨tr₁, hdrv⟩ := drive_loop_sync_op_context (table := table) root ctx o K i s k tr nt [Cmd.drainDue] s₁ v hk hso
                have hstep : localStep root (fiberOf (Prim.sync (.op o)) K i) s =
                    .running (fiberOf (Prim.success v) K i) s₁ := by rw [step_sync_op, hso]
                apply recurse 2 (by decide) _ K i s₁ (k + 1) tr₁ ctx true rfl hK hq₁
                  (fun _ => ⟨(fun _ h => by cases h), rfl⟩)
                  (ReachesQ.step hstep rfl (fun _ h => by cases h))
                intro n
                simp only [cmdOf]
                rw [show n + 2 = n + 1 + 1 by omega, hdrv,
                  drive_drainDue root _ _ _ rfl hq₁]
      · have hp : (stores.budgetOf ctx).2 = false := by
          cases h : (stores.budgetOf ctx).2
          · rfl
          · exact (hk (Or.inl h)).elim
        have hbudget : (stores.budgetOf ctx).1 ≤ k + 1 := by omega
        obtain ⟨tr₁, hdrv⟩ := drive_loop_yield_context (table := table) root cur K i s k tr nt [Cmd.drainDue] ctx hp hbudget
        refine ⟨Myield (fiberOf cur K i) s (k + 2) tr₁ nt ctx, ?_, ?_⟩
        · apply drive_receipt_result root fuel 3 _ _ _ hreceipt
          intro n
          simp only [cmdOf]
          rw [show n + 3 = (n + 1) + 2 by omega, hdrv,
            drive_drainDue root _ _ _ rfl hq, drive_nil]
        · exact Or.inr (Or.inr ⟨cur, K, i, s, k + 2, tr₁, nt, ctx, rfl, hpl, hK, hq,
            0, ReachesQ.refl root _ _ ctx⟩)

end Effect4.Program.Agreement
