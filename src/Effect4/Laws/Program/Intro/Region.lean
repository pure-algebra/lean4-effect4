import Effect4.Laws.Program.Intro.AcquireRelease

/-!
# Intro.Region: regions, context updates and scope registration (the join)

The memo protocol's finalizers, a region under the restoring finalizer, `updateContext` and
`scopeAddFinalizerExit`, one lemma per named continuation.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## The join: `Effect.provide`, `Effect.service`, `Effect.provideService`, `Layer.build`

Step by step as `acquireRelease` (V1): one lemma per named continuation, the layer build by
structural recursion on the layer term (`layer_intro`), the memo protocol's three finalizers
proved here so the build needs nothing of `Simulation/Hooks.lean`. -/

/-- The stores' `closeIfLast` on anything but a scope handle: done (`Layer.ts:408`). -/
theorem contAOf_closeIfLast_other (ex : ExitV) (v : Val) (hne : ∀ s, v ≠ Val.scopeHandle s) :
    Effect4.Machine.contAOf (Name.closeIfLast ex) v = Prim.success Val.unit := by
  simp only [Effect4.Machine.contAOf]

/-- `fromBuild`'s `onExit` (`Layer.ts:343`): close the layer scope on failure only. -/
theorem closeChildOnFailure_means (root : NativeEff) (child : Nat) (ex : ExitV) :
    CodeMeans root (embed (finProgram (.closeChildOnFailure child) ex))
      (denoteFin (.closeChildOnFailure child) ex) := by
  cases ex with
  | failure cause =>
    simp only [finProgram, embed, denoteFin]
    exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | success v =>
    simp only [finProgram, embed, denoteFin]
    exact CodeMeans.success _

/-- The memo entry finalizer (`Layer.ts:401-410`): `observers--`; the last observer's release
answers the layer scope, closed with the exit. -/
theorem memoEntry_means (root : NativeEff) (layer : LayerId) (memoMap : MemoMapId) (ex : ExitV) :
    CodeMeans root (embed (finProgram (.memoEntry layer memoMap) ex))
      (denoteFin (.memoEntry layer memoMap) ex) := by
  simp only [finProgram, embed, denoteFin]
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.memoRelease layer memoMap)) _
    (CodeMeans.syncStore _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  show CodeMeans root (embed (Effect4.Machine.contAOf (Name.closeIfLast ex) v)) _
  cases hs : Val.scope? v with
  | some s =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (embed (Prim.withFiber (Thunk.act (ActionName.closeScope s ex)))) _
    exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | none =>
    rw [contAOf_closeIfLast_other ex v (Val.scope?_none hs)]
    simp only [embed, prepareR_pure]
    exact CodeMeans.success _

/-- `memoMapBuild`'s `onExit` (`Layer.ts:414-417`): the exit stored, the Deferred completed. -/
theorem memoDone_means (root : NativeEff) (layer : LayerId) (memoMap : MemoMapId) (ex : ExitV) :
    CodeMeans root (embed (finProgram (.memoDone layer memoMap) ex))
      (denoteFin (.memoDone layer memoMap) ex) := by
  simp only [finProgram, embed, denoteFin]
  exact CodeMeans.syncStore _ _ (successV root)

/-- A region under the finalizer that restores the previous context (`updateContext`,
`internal/effect.ts:2092-2095`): `release_intro` on any region. -/
theorem region_intro (root : NativeEff) (body : Region) (previous : Ctx) (r : RProgram)
    (hb : CodeMeans root (regionCode root body) r) :
    CodeMeans root (Prim.onExit (regionCode root body) (.restoreCtx previous) false)
      (onExitR r fun _ => fiberValR (.setContext previous) rfl) := by
  unfold onExitR
  rw [guardR_bind]
  refine CodeMeans.onExit _ _ _ r
    (fun ex => finalizerR ex (fiberValR (.setContext previous) rfl)) hb ?_ (fun _ _ => rfl) rfl
    (fun _ => rfl)
  intro completed ex program hprog
  have hp' : Prim.withFiber (EffThunk.setCtx previous) = program := Option.some.inj hprog
  rw [← hp']
  refine finalizer_intro root completed ex ?_
  exact CodeMeans.actSetContext _ _ _ rfl (successV root)

/-- `updateContext(self, f)` (`internal/effect.ts:2087-2096`): the context read, the identity
shortcut or the set-and-restore region. -/
theorem updateContext_intro (root : NativeEff) (u : Env.ContextUpdate) (body : Region)
    (r : RProgram) (hb : CodeMeans root (regionCode root body) r) :
    CodeMeans root (updateContextAt u body) (updateContextR u r) := by
  unfold updateContextAt updateContextR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _
    (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.updateThen u body) v) _
  rw [contAOf_updateThen]
  unfold updateThenK
  simp only [seqR]
  cases hctx : Val.context? v with
  | some prev =>
    dsimp only
    by_cases hid : updateKeepsIdentity u prev.services = true
    · simp only [hid, ↓reduceIte]
      exact hb.prepare completed
    · simp only [hid, Bool.false_eq_true, ↓reduceIte]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _
        (prepareR completed
          (fiberValR (.setContext (Ctx.withServices (u.apply prev.services))) rfl)) _
        (CodeMeans.actSetContext _ _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
      intro completed' _
      show CodeMeans root (Program.contAOf root (.bodyThen body prev) _) _
      rw [contAOf_bodyThen]
      simp only [seqR]
      exact (region_intro root body prev r hb).prepare completed'
  | none => exact codeMeans_badShape root

/-- `scopeAddFinalizerExit(scope, fin)` (`internal/effect.ts:3847-3858`): the registration,
then unit, or the finalizer now when the scope had already closed. -/
theorem scopeAdd_intro (root : NativeEff) (scope : Nat) (fin : FinName)
    (hfin : ∀ ex, CodeMeans root (embed (finProgram fin ex)) (denoteFin fin ex)) :
    CodeMeans root (scopeAddAt scope fin) (scopeAddR scope fin) := by
  unfold scopeAddAt scopeAddR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeAdd scope fin)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed w
  show CodeMeans root (Program.contAOf root (.afterScopeAdd Val.unit fin) w) _
  rw [contAOf_afterScopeAdd]
  simp only [seqR]
  by_cases hw : w = Val.unit
  · rw [if_pos hw, if_pos hw, prepareR_pure]
    exact CodeMeans.success _
  · rw [if_neg hw, if_neg hw]
    cases hex : exitOfVal w with
    | some ex =>
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed (denoteFin fin ex)) _
        ((hfin ex).prepare _) ?_ rfl (fun _ => rfl)
      intro completed' _
      show CodeMeans root (Prim.success Val.unit) _
      simp only [seqR, prepareR_pure]
      exact CodeMeans.success _
    | none => exact codeMeans_badShape root


end Effect4.Program.Sched
