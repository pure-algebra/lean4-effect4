import Effect4.Laws.Program.Intro.Region

/-!
# Intro.Memo: `fromBuild`, `getOrElseMemoize`, `buildWithMemoMap` and `provideWith`

The layer scope forked and closed on failure, the memo lookup with its hit and miss, the
`CurrentMemoMap` region and the dependency/dependent combiner.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-- `fromBuild` (`Layer.ts:333-345`): the layer scope forked from the caller's, the inner build
inside it under the finalizer that closes it on failure. -/
theorem fromBuild_intro (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat)
    (innerR : Nat → RProgram)
    (hinner : ∀ child, CodeMeans root (innerLayerAt root q m child) (innerR child)) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m))
      (fromBuildR scope innerR) := by
  unfold fromBuildR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeFork scope .sequential)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some child =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.fromBuildThen q m) (Val.scopeHandle child)) _
    rw [contAOf_fromBuildThen_scope]
    dsimp only
    unfold onExitR
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onExit _ _ _ (prepareR completed (innerR child))
      (fun ex => finalizerR ex (denoteFin (.closeChildOnFailure child) ex))
      ((hinner child).prepare _) ?_ (fun _ _ => rfl) rfl (fun _ => rfl)
    intro completed' ex program hprog
    have hp' : embed (finProgram (.closeChildOnFailure child) ex) = program :=
      Option.some.inj hprog
    rw [← hp']
    exact finalizer_intro root completed' ex ((closeChildOnFailure_means root child ex).prepare _)
  | none =>
    show CodeMeans root (Program.contAOf root (.fromBuildThen q m) v) _
    rw [contAOf_fromBuildThen_other root q m v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

/-- `getOrElseMemoize` (`Layer.ts:445-457`): the counted suspend, the lookup, a hit's
registration and await, or `memoMapBuild` over the construction. -/
theorem memoize_intro (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat)
    (constructionR : Nat → RProgram)
    (hcons : ∀ layerScope,
      CodeMeans root (constructionAt root q layerScope) (constructionR layerScope)) :
    CodeMeans root (Prim.suspend (EffThunk.memoLookup q m scope))
      (memoizeR q m scope constructionR) := by
  unfold memoizeR suspendR
  refine CodeMeans.suspendMemo q m scope _ fun completed => ?_
  rw [suspendBodyAt_memoLookup, prepareR_guardR_bind, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (prepareR completed (storeR (.memoGet q.path m))) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed' v
  simp only [seqR]
  cases hhit : Val.memoHit? v with
  | some co =>
    obtain ⟨cell, owner⟩ := co
    have hv := Val.memoHit?_exact hhit
    subst hv
    show CodeMeans root
      (Program.contAOf root (.memoize q m scope) (.pair (Val.promise cell) (Val.memoMap owner))) _
    rw [contAOf_memoize_hit]
    dsimp only
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _
      (prepareR completed' (scopeAddR scope (.memoEntry q.path owner))) _
      ((scopeAdd_intro root scope _ (memoEntry_means root _ _)).prepare _) ?_ rfl (fun _ => rfl)
    intro completed'' _
    show CodeMeans root (Program.contAOf root (.awaitPromise cell) _) _
    rw [contAOf_awaitPromise]
    simp only [seqR]
    exact CodeMeans.asyncAwait cell (Val.promise cell) _ delivers_pure
  | none =>
    have hne := Val.memoHit?_none hhit
    by_cases hu : v = Val.unit
    · subst hu
      rw [if_pos rfl]
      show CodeMeans root (Program.contAOf root (.memoize q m scope) Val.unit) _
      rw [contAOf_memoize_unit]
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed' (storeR (.memoBuild q.path m))) _
        (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
      intro completed'' w
      simp only [seqR]
      cases hls : Val.scope? w with
      | some layerScope =>
        have hw := Val.scope?_exact hls
        subst hw
        show CodeMeans root
          (Program.contAOf root (.buildIntoLayerScope q m scope) (Val.scopeHandle layerScope)) _
        rw [contAOf_buildIntoLayerScope_scope]
        dsimp only
        rw [prepareR_guardR_bind, guardR_bind]
        refine CodeMeans.onSuccess _ _ _
          (prepareR completed'' (scopeAddR scope (.memoEntry q.path m))) _
          ((scopeAdd_intro root scope _ (memoEntry_means root _ _)).prepare _) ?_ rfl
          (fun _ => rfl)
        intro completed''' _
        show CodeMeans root (Program.contAOf root (.thenBuildInto q m layerScope) _) _
        rw [contAOf_thenBuildInto]
        simp only [seqR]
        unfold onExitR
        rw [prepareR_guardR_bind, guardR_bind]
        refine CodeMeans.onExit _ _ _ (prepareR completed''' (constructionR layerScope))
          (fun ex => finalizerR ex (denoteFin (.memoDone q.path m) ex))
          ((hcons layerScope).prepare _) ?_ (fun _ _ => rfl) rfl (fun _ => rfl)
        intro completed'''' ex program hprog
        have hp' : embed (finProgram (.memoDone q.path m) ex) = program := Option.some.inj hprog
        rw [← hp']
        exact finalizer_intro root completed'''' ex ((memoDone_means root _ _ ex).prepare _)
      | none =>
        show CodeMeans root (Program.contAOf root (.buildIntoLayerScope q m scope) w) _
        rw [contAOf_buildIntoLayerScope_other root q m scope w (Val.scope?_none hls)]
        simp only [prepareR_pure]
        exact codeMeans_badShape root
    · rw [if_neg hu]
      show CodeMeans root (Program.contAOf root (.memoize q m scope) v) _
      rw [contAOf_memoize_other root q m scope v hne hu]
      simp only [prepareR_pure]
      exact codeMeans_badShape root

/-- `buildWithMemoMap` (`Layer.ts:756-765`): the `CurrentMemoMap` region over the build, its
answer with the map added. -/
theorem buildWithMemoMap_intro (root : NativeEff) (q : Point) (scope : Nat)
    (buildR : MemoMapId → RProgram)
    (hb : ∀ m, CodeMeans root (resolveLayer root q m scope) (buildR m)) (id : MemoMapId) :
    CodeMeans root
      (updateContextAt (Env.ContextUpdate.provideService Env.currentMemoMapKey (Val.memoMap id))
        (Region.buildAdding q id scope))
      (buildWithMemoMapR buildR id) := by
  unfold buildWithMemoMapR
  refine updateContext_intro root _ _ _ ?_
  simp only [regionCode]
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (buildR id) _ (hb id) ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.addCurrentMemoMap id) v) _
  rw [contAOf_addCurrentMemoMap]
  unfold addCurrentMemoMapK addCurrentMemoMapR
  simp only [seqR]
  cases Env.decode v with
  | some ctx => simp only [prepareR_pure]; exact CodeMeans.success _
  | none => exact codeMeans_badShape root

/-- The memo map forked or created, in hand: `buildWithMemoMap` on it, or the wrong shape. -/
theorem withMemoMapThen_intro (root : NativeEff) (q : Point) (scope : Nat)
    (buildR : MemoMapId → RProgram)
    (hb : ∀ m, CodeMeans root (resolveLayer root q m scope) (buildR m))
    (completed : List (FiberId × ExitV)) (u : Val) :
    CodeMeans root (Program.contAOf root (.withMemoMapThen q scope) u)
      (prepareR completed (match Val.memoMap? u with
        | some id => buildWithMemoMapR buildR id
        | none => .pure badShapeExit)) := by
  cases hid : Val.memoMap? u with
  | some id =>
    have hu := Val.memoMap?_exact hid
    subst hu
    rw [contAOf_withMemoMapThen_memoMap]
    dsimp only
    exact (buildWithMemoMap_intro root q scope buildR hb id).prepare completed
  | none =>
    rw [contAOf_withMemoMapThen_other root q scope u (Val.memoMap?_none hid)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

/-- `provideWith` (`Layer.ts:1915-1923`): the dependency built, the dependent under its
context, the combiner. -/
theorem provideWith_intro (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat)
    (mode : CombineMode) (depR depdR : RProgram)
    (hdep : CodeMeans root (resolveLayer root (q.child 1) m child) depR)
    (hdept : CodeMeans root (resolveLayer root (q.child 0) m child) depdR) :
    CodeMeans root
      (Prim.onSuccess (resolveLayer root (q.child 1) m child) (.provideThen q m child mode))
      (provideWithR depR depdR mode) := by
  unfold provideWithR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ depR _ hdep ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.provideThen q m child mode) v) _
  rw [contAOf_provideThen]
  unfold provideThenK
  simp only [seqR]
  cases hd : Env.decode v with
  | some ctx =>
    dsimp only
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (prepareR completed (updateContextR (.provide ctx) depdR)) _
      ((updateContext_intro root _ (Region.build (q.child 0) m child) depdR hdept).prepare _) ?_
      rfl (fun _ => rfl)
    intro completed' w
    show CodeMeans root (Program.contAOf root (.combineWith mode ctx) w) _
    rw [contAOf_combineWith]
    unfold combineWithK combineWithR
    simp only [seqR]
    cases Env.decode w with
    | some merged => cases mode <;> (simp only [prepareR_pure]; exact CodeMeans.success _)
    | none => exact codeMeans_badShape root
  | none => exact codeMeans_badShape root


end Effect4.Program.Sched
