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

/-- The existing restoring-context frame wraps any related body code.
Consumer: region_intro and the masked provider body's finalizer placement. -/
theorem restoreContext_intro (root : NativeEff) (body : NCode) (previous : Ctx) (r : RProgram)
    (hb : CodeMeans root body r) :
    CodeMeans root (Prim.onExit body (.restoreCtx previous) false)
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

/-- A region under the finalizer that restores its previous context.
Consumer: the existing layer region producers. -/
theorem region_intro (root : NativeEff) (body : Region) (previous : Ctx) (r : RProgram)
    (hb : CodeMeans root (regionCode root body) r) :
    CodeMeans root (Prim.onExit (regionCode root body) (.restoreCtx previous) false)
      (onExitR r fun _ => fiberValR (.setContext previous) rfl) :=
  restoreContext_intro root (regionCode root body) previous r hb

/-- The body restore action uses the existing mask constructor and its actual Region body.
Consumer: contextEntry_intro on both identity and setter paths. -/
theorem restoreRegion_intro (root : NativeEff) (body : Region) (flag : Bool)
    (hb : CodeMeans root (regionCode root body) (denoteBody root (.region body))) :
    CodeMeans root (.withFiber (.restoreRegion body flag)) (restoreRegionR body flag) :=
  CodeMeans.actMask _ _ flag (.region body) _ rfl hb delivers_pure

/-- The protected provider half places the context-restoring frame before restoring the body mask.
Consumer: updateContext_intro and the existing provider source agreement. -/
theorem contextEntry_intro (root : NativeEff) (u : Env.ContextUpdate) (body : Region) (flag : Bool)
    (hb : CodeMeans root (regionCode root body) (denoteBody root (.region body))) :
    CodeMeans root (.onSuccess (.withFiber .getCtx) (.updateThen u body flag))
      (contextEntryR u body flag) := by
  unfold contextEntryR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _
    (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.updateThen u body flag) v) _
  rw [contAOf_updateThen]
  unfold updateThenK
  simp only [seqR]
  cases hctx : Val.context? v with
  | some prev =>
    dsimp only
    by_cases hid : updateKeepsIdentity u prev.services = true
    · simp only [hid, ↓reduceIte]
      exact (restoreRegion_intro root body flag hb).prepare completed
    · simp only [hid, Bool.false_eq_true, ↓reduceIte]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _
        (prepareR completed
          (fiberValR (.setContext (Ctx.withServices (u.apply prev.services))) rfl)) _
        (CodeMeans.actSetContext _ _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
      intro completed' _
      show CodeMeans root (Program.contAOf root (.bodyThen body prev flag) _) _
      rw [contAOf_bodyThen]
      simp only [seqR]
      exact (restoreContext_intro root (.withFiber (.restoreRegion body flag)) prev
        (restoreRegionR body flag) (restoreRegion_intro root body flag hb)).prepare completed'
  | none => exact codeMeans_badShape root

/-- Capture the caller's mask, then enter the existing protected provider body.
Consumer: the source provider agreement; the actual Region body premise replaces arbitrary RProgram reach. -/
theorem updateContext_intro (root : NativeEff) (u : Env.ContextUpdate) (body : Region)
    (hb : CodeMeans root (regionCode root body) (denoteBody root (.region body))) :
    CodeMeans root (updateContextAt u body) (updateContextR u body) := by
  unfold updateContextAt updateContextR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .getInterruptible rfl) _
    (CodeMeans.actGetInterruptible _ _ rfl delivers_seqR_pure) ?_ rfl (fun _ => rfl)
  intro completed value
  show CodeMeans root (Program.contAOf root (.provideMask u body) value) _
  simp only [Program.contAOf, seqR]
  cases decoded : Val.savedMask? value with
  | none => exact codeMeans_badShape root
  | some flag =>
    exact CodeMeans.actMask _ _ false (.contextEntry u body flag) _ rfl
      (contextEntry_intro root u body flag hb) delivers_pure

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
