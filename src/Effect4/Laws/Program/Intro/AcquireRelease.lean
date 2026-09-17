import Effect4.Laws.Program.Intro.Weight

/-!
# Intro.AcquireRelease: `acquireRelease`'s pieces (V1)

The release under the context-restoring finalizer, a capture's counted release and the
masked half of the acquire, each against its term given the related code at its points.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## The introduction -/

/-- The `forkScoped` node's payload, read decidably (the case split of `code_intro_aux`
stays at the ceiling: no classical choice on an existential). -/
def forkScoped? : ActionTerm NativeOp → Option (NativeEff × Supervision.ForkOptions)
  | .forkScoped child options => some (child, options)
  | _ => none

theorem forkScoped?_some {a : ActionTerm NativeOp} {child : NativeEff}
    {options : Supervision.ForkOptions} (h : forkScoped? a = some (child, options)) :
    a = .forkScoped child options := by
  cases a with
  | forkScoped c o =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  | _ => exact nomatch h

theorem forkScoped?_none {a : ActionTerm NativeOp} (h : forkScoped? a = none) :
    ∀ c o, a ≠ .forkScoped c o := by
  intro c o heq
  subst heq
  exact nomatch h

/-! ### `acquireRelease`'s pieces (V1)

The release at its point under the context-restoring finalizer, the counted suspend of a
capture's release, and the masked half of the acquire — each against its `Body` or
`denoteFin` term, given the related code at the points they resolve. -/

/-- `provideContext(release(a, exit), context)`'s frame (`internal/effect.ts:2180-2199`): the
release under the finalizer that restores the previous context. -/
theorem release_intro (root : NativeEff) (q : Point) (previous : Ctx)
    (hres : CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (Prim.onExit (resolve root q) (.restoreCtx previous) false)
      (denoteBody root (.release q previous)) := by
  show CodeMeans root _ (onExitR (denoteAt root q) fun _ => fiberValR (.setContext previous) rfl)
  unfold onExitR
  rw [guardR_bind]
  refine CodeMeans.onExit _ _ _ (denoteAt root q)
    (fun ex => finalizerR ex (fiberValR (.setContext previous) rfl)) hres ?_ (fun _ _ => rfl) rfl
    (fun _ => rfl)
  intro completed ex program hprog
  have hp' : Prim.withFiber (EffThunk.setCtx previous) = program := Option.some.inj hprog
  rw [← hp']
  refine finalizer_intro root completed ex ?_
  -- `prepareR` is the identity on the `setContext` operation, definitionally
  exact CodeMeans.actSetContext _ _ _ rfl (successV root)

/-- A capture's release (`FinName.foreign`): the counted suspend, the context read, the
captured context set, then the release masked at the capture's point over the exit — the
point refreshed with the view at the release's invocation on both sides. -/
theorem foreignRelease_intro (root : NativeEff) (c : Capture) (ex : ExitV)
    (hres : ∀ completed, CodeMeans root
      (resolve root ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)))
      (denoteAt root ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)))) :
    CodeMeans root (embed (finProgram (.foreign c) ex)) (denoteFin (.foreign c) ex) := by
  simp only [finProgram, embed, denoteFin]
  refine CodeMeans.foreignRelease c ex _ fun completed => ?_
  simp only [suspendBodyAt]
  rw [prepareR_guardR_bind, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (prepareR completed (fiberValR .getContext rfl)) _ ?_ ?_ rfl
    (fun _ => rfl)
  · exact CodeMeans.actGetContext _ _ rfl (successV root)
  · intro completed' v
    show CodeMeans root (Program.contAOf root (.releaseUnder (Point.ofCapture c) c.ctx ex) v) _
    rw [contAOf_releaseUnder]
    simp only [seqR]
    -- the current context read back off the value, or not
    cases hctx : Val.context? v with
    | some previous =>
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed' (fiberValR (.setContext c.ctx) rfl)) _
        ?_ ?_ rfl (fun _ => rfl)
      · exact CodeMeans.actSetContext _ _ _ rfl (successV root)
      · intro completed'' w
        show CodeMeans root
          (Program.contAOf root
            (.releaseBody { Point.ofCapture c with completed := completed'' } ex previous) w) _
        rw [contAOf_releaseBody]
        simp only [seqR, prepareR_constructR]
        -- `prepareR` is the identity on the mask operation, definitionally; the two release
        -- points are the capture's point at this view, spelled two ways
        exact CodeMeans.actMask _ _ false (.release _ previous) _ rfl
          (release_intro root _ previous (hres completed'')) delivers_pure
    | none => exact codeMeans_badShape root

/-- `uninterruptibleMask(restore => flatMap(scope, scope => tap(acquire, scopeAddFinalizerExit
…)))` (`internal/effect.ts:3977-3986`): the masked half, given the acquire at the point's
child 0 and the capture's release. -/
theorem acquireIn_intro (root : NativeEff) (p : Point) (ctx : Ctx)
    (hres : CodeMeans root (resolve root (p.child 0)) (denoteAt root (p.child 0)))
    (hfin : ∀ (a : Val) (ex : ExitV),
      CodeMeans root (embed (finProgram (.foreign (p.capture a ctx)) ex))
        (denoteFin (.foreign (p.capture a ctx)) ex)) :
    CodeMeans root
      (Prim.onSuccess (Prim.withFiber (.store (.act .ambientScope))) (.acquireIn p ctx))
      (denoteBody root (.acquireIn p ctx)) := by
  show CodeMeans root _ (acquireInR (denoteAt root (p.child 0)) p ctx)
  unfold acquireInR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .ambientScope rfl) _ ?_ ?_ rfl (fun _ => rfl)
  · exact CodeMeans.actAmbientScope _ _ rfl (successV root)
  · intro completed v
    -- the handle the service read answered is a scope handle or it is not
    cases hsc : Val.scope? v with
    | some s =>
      have hv := Val.scope?_exact hsc
      subst hv
      show CodeMeans root (Prim.onSuccess (resolve root (p.child 0)) (.acquired p ctx s)) _
      simp only [seqR, Val.scope?_scopeHandle]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed (denoteAt root (p.child 0))) _
        (hres.prepare _) ?_ rfl (fun _ => rfl)
      intro completed' a
      show CodeMeans root (Program.contAOf root (.acquired p ctx s) a) _
      rw [contAOf_acquired]
      simp only [seqR]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _
        (prepareR completed' (storeR (.scopeAdd s (.foreign (p.capture a ctx))))) _
        (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
      intro completed'' w
      show CodeMeans root (Program.contAOf root (.afterScopeAdd a (.foreign (p.capture a ctx))) w) _
      rw [contAOf_afterScopeAdd]
      simp only [seqR]
      -- unit: the registration took; anything else is the closing exit, read back or not
      by_cases hw : w = Val.unit
      · rw [if_pos hw, if_pos hw, prepareR_pure]
        exact CodeMeans.success a
      · rw [if_neg hw, if_neg hw]
        cases hex : exitOfVal w with
        | some ex =>
          dsimp only
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _
            (prepareR completed'' (denoteFin (.foreign (p.capture a ctx)) ex)) _
            ((hfin a ex).prepare _) ?_ rfl (fun _ => rfl)
          intro completed''' _
          show CodeMeans root (Prim.success a) _
          simp only [seqR, prepareR_pure]
          exact CodeMeans.success a
        | none => exact codeMeans_badShape root
    | none =>
      have hne : ∀ s, v ≠ Val.scopeHandle s := Val.scope?_none hsc
      show CodeMeans root (Program.contAOf root (.acquireIn p ctx) v) _
      rw [contAOf_acquireIn_other root ctx v hne]
      simp only [seqR, hsc, prepareR_pure]
      exact codeMeans_badShape root

end Effect4.Program.Sched
