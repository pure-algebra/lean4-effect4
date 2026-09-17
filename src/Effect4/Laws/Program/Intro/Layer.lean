import Effect4.Laws.Program.Intro.Merge

/-!
# Intro.Layer: a layer's build and `Effect.provide`

The structural pass over the layer term with a reference's hop taken at less fuel
(`layerTerm_intro`), closed by induction on the fuel (`layer_intro`), and `provideLayer`'s
protocol after its counted step.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## A layer's build

The recursion is structural in the layer term, with one hypothesis it cannot discharge by
structure: a reference (`LayerTerm.ref`, the host rows slice) hops to its target's term, which
is no subterm, one fuel down. So the structural pass takes every layer at strictly less fuel
as given (`hhop`), and `layer_intro` closes it by induction on the fuel. The layers of a
`mergeAll` are the spine's elements at their own points (`Point.spineChild`), walked with the
spine (`layerTerms_intro`). -/

mutual
/-- **A layer's build**, the structural pass. At its point, the frame's
`resolveLayer.resolveLayerTerm` and the term's `denoteLayer` are related, given every program
at a lighter point (`hres`) and every layer at strictly less fuel (`hhop`). -/
theorem layerTerm_intro (root : NativeEff) (n : Nat)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q))
    (K : Nat)
    (hhop : ∀ (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat),
      q.fuel < K → q.weight < n → Node.at_ (.eff root) q.path = some (.layer l) →
      CodeMeans root (resolveLayer.resolveLayerTerm root l q m scope) (denoteLayer root l q m scope)) :
    ∀ (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat), q.fuel ≤ K →
      q.weight < n → Node.at_ (.eff root) q.path = some (.layer l) →
      CodeMeans root (resolveLayer.resolveLayerTerm root l q m scope) (denoteLayer root l q m scope)
  | .succeed key value, q, m, scope, _, _, _ => by
    rw [resolveLayerTerm_of_nonref root (.succeed key value) q m scope nofun, denoteLayer_succeed]
    simp only [compileLayer]
    cases Lit.toVal value with
    | some v => exact CodeMeans.success _
    | none => exact codeMeans_badShape root
  | .fresh inner, q, m, scope, hK, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.fresh inner) q m scope nofun, compileLayer_fresh,
      denoteLayer_fresh, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (storeR (.memoFork none)) _
      (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
    intro completed v
    simp only [seqR]
    have hinner := at_child_of h 0
    cases hid : Val.memoMap? v with
    | some id =>
      have hv := Val.memoMap?_exact hid
      subst hv
      show CodeMeans root (Program.contAOf root (.freshThen (q.child 0) scope) (Val.memoMap id)) _
      rw [contAOf_freshThen_memoMap, resolveLayer_of_at root hinner]
      dsimp only
      exact (layerTerm_intro root n hres K hhop inner (q.child 0) id scope
        (Nat.le_trans (fuel_child_le q 0) hK) (Nat.lt_of_le_of_lt (weight_child q 0) hq)
        hinner).prepare completed
    | none =>
      show CodeMeans root (Program.contAOf root (.freshThen (q.child 0) scope) v) _
      rw [contAOf_freshThen_other root _ _ v (Val.memoMap?_none hid)]
      simp only [prepareR_pure]
      exact codeMeans_badShape root
  | .orDie inner, q, m, scope, hK, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.orDie inner) q m scope nofun, compileLayer_orDie,
      denoteLayer_orDie, guardR_bind]
    have hinner := at_child_of h 0
    have ih := layerTerm_intro root n hres K hhop inner (q.child 0) m scope
      (Nat.le_trans (fuel_child_le q 0) hK) (Nat.lt_of_le_of_lt (weight_child q 0) hq) hinner
    refine CodeMeans.onFailure _ _ _
      (if inner.isRef then .pure badShapeExit else denoteLayer root inner (q.child 0) m scope) _
      ?_ ?_ rfl (fun _ => rfl)
    · -- the inner term is compiled at the table directly: a reference is the refusal on
      -- both sides, every other constructor its own build
      cases inner with
      | ref target => exact codeMeans_badShape root
      | _ => exact ih
    · intro completed c
      show CodeMeans root (Prim.failure (orDieCause c))
        (prepareR completed (.pure (.failure (orDieCause c))))
      rw [prepareR_pure]
      exact CodeMeans.failure _
  | .effect key body, q, m, scope, _, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.effect key body) q m scope nofun, compileLayer_effect,
      denoteLayer_effect]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_effect root h]
    refine memoize_intro root q m child _ fun layerScope => ?_
    rw [constructionAt_effect root h]
    refine updateContext_intro root _ (Region.construct (q.child 0) (some key)) _ ?_
    simp only [regionCode]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (denoteR root body (q.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
    · have hb := at_child_of h 0
      have hr := hres (q.child 0) (Nat.lt_of_le_of_lt (weight_child q 0) hq)
      rw [denoteAt_of_at hb] at hr
      exact hr
    · intro completed v
      show CodeMeans root (Program.contAOf root (.bindService (some key)) v) _
      rw [contAOf_bindService]
      simp only [seqR, bindServiceK, bindServiceR, prepareR_pure]
      exact CodeMeans.success _
  | .effectDiscard body, q, m, scope, _, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.effectDiscard body) q m scope nofun,
      compileLayer_effectDiscard, denoteLayer_effectDiscard]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_effectDiscard root h]
    refine memoize_intro root q m child _ fun layerScope => ?_
    rw [constructionAt_effectDiscard root h]
    refine updateContext_intro root _ (Region.construct (q.child 0) none) _ ?_
    simp only [regionCode]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (denoteR root body (q.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
    · have hb := at_child_of h 0
      have hr := hres (q.child 0) (Nat.lt_of_le_of_lt (weight_child q 0) hq)
      rw [denoteAt_of_at hb] at hr
      exact hr
    · intro completed v
      show CodeMeans root (Program.contAOf root (.bindService none) v) _
      rw [contAOf_bindService]
      simp only [seqR, bindServiceK, bindServiceR, prepareR_pure]
      exact CodeMeans.success _
  | .provide self that, q, m, scope, hK, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.provide self that) q m scope nofun, compileLayer_provide,
      denoteLayer_provide]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_provide root h]
    have hs := at_child_of h 0
    have ht := at_child_of h 1
    refine provideWith_intro root q m child .provide _ _ ?_ ?_
    · rw [resolveLayer_of_at root ht]
      exact layerTerm_intro root n hres K hhop that (q.child 1) m child
        (Nat.le_trans (fuel_child_le q 1) hK) (Nat.lt_of_le_of_lt (weight_child q 1) hq) ht
    · rw [resolveLayer_of_at root hs]
      exact layerTerm_intro root n hres K hhop self (q.child 0) m child
        (Nat.le_trans (fuel_child_le q 0) hK) (Nat.lt_of_le_of_lt (weight_child q 0) hq) hs
  | .provideMerge self that, q, m, scope, hK, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.provideMerge self that) q m scope nofun,
      compileLayer_provideMerge, denoteLayer_provideMerge]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_provideMerge root h]
    have hs := at_child_of h 0
    have ht := at_child_of h 1
    refine provideWith_intro root q m child .provideMerge _ _ ?_ ?_
    · rw [resolveLayer_of_at root ht]
      exact layerTerm_intro root n hres K hhop that (q.child 1) m child
        (Nat.le_trans (fuel_child_le q 1) hK) (Nat.lt_of_le_of_lt (weight_child q 1) hq) ht
    · rw [resolveLayer_of_at root hs]
      exact layerTerm_intro root n hres K hhop self (q.child 0) m child
        (Nat.le_trans (fuel_child_le q 0) hK) (Nat.lt_of_le_of_lt (weight_child q 0) hq) hs
  | .merge left right, q, m, scope, hK, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.merge left right) q m scope nofun, compileLayer_merge,
      denoteLayer_merge]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_merge root h]
    have h0 := at_child_of h 0
    have h1 := at_child_of h 1
    refine mergeTwo_intro root q m child ?_ ?_
    · intro c
      rw [resolveLayer_of_at root h0, layerBuildR_of_at h0]
      exact layerTerm_intro root n hres K hhop left (q.child 0) m c
        (Nat.le_trans (fuel_child_le q 0) hK) (Nat.lt_of_le_of_lt (weight_child q 0) hq) h0
    · intro c
      rw [resolveLayer_of_at root h1, layerBuildR_of_at h1]
      exact layerTerm_intro root n hres K hhop right (q.child 1) m c
        (Nat.le_trans (fuel_child_le q 1) hK) (Nat.lt_of_le_of_lt (weight_child q 1) hq) h1
  | .mergeAll layers, q, m, scope, hK, hq, h => by
    rw [resolveLayerTerm_of_nonref root (.mergeAll layers) q m scope nofun, compileLayer_mergeAll,
      denoteLayer_mergeAll]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_mergeAll root h]
    refine mergeAll_intro root q m child layers.length (mergeAllCount_of_at root h) ?_
    intro i hi c
    rw [Point.spineChild_eq]
    exact layerTerms_intro root n hres K hhop layers (q.child 0) i hi
      (Nat.le_trans (fuel_child_le q 0) hK) (Nat.lt_of_le_of_lt (weight_child q 0) hq)
      (at_child_of h 0) m c
  | .ref target, q, m, scope, hK, hq, _ => by
    rw [resolveLayerTerm_ref]
    cases hf : q.fuel with
    | zero =>
      -- no fuel for the hop: the live frontier at the reference's point, on both sides
      rw [denoteLayer_ref_zero root target q m scope hf]
      exact CodeMeans.frontier q q _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ fun completed => by
        rw [suspendBodyAt_zero' (q := { q with completed }) hf]; rfl
    | succ k =>
      -- the hop: the target's term at the target's path, one fuel down, given by `hhop`; a
      -- target that is a reference itself, or no layer, is the wrong shape on both sides
      rw [denoteLayer_ref_succ root target q m scope hf]
      have hw : (q.redirect target).weight < n :=
        Nat.lt_of_le_of_lt (weight_redirect_le q target) hq
      have hk : (q.redirect target).fuel < K := by
        rw [Point.redirect_fuel, hf]; omega
      rcases hn : Node.at_ (Node.eff root) target with _ | node
      · exact codeMeans_badShape root
      · cases node with
        | layer l' =>
          have ih := hhop l' (q.redirect target) m scope hk hw hn
          cases l' with
          | ref target' => exact codeMeans_badShape root
          | _ => exact ih
        | _ => exact codeMeans_badShape root
termination_by structural l => l

/-- The layers of a `mergeAll`'s spine, each built at its own point: the `i`-th layer of the
spine at `p` is the head of the spine walked `i` steps in (`Point.spineWalk`). -/
theorem layerTerms_intro (root : NativeEff) (n : Nat)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q))
    (K : Nat)
    (hhop : ∀ (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat),
      q.fuel < K → q.weight < n → Node.at_ (.eff root) q.path = some (.layer l) →
      CodeMeans root (resolveLayer.resolveLayerTerm root l q m scope) (denoteLayer root l q m scope)) :
    ∀ (ls : LayerTerms NativeOp) (p : Point) (i : Nat), i < ls.length → p.fuel ≤ K →
      p.weight < n → Node.at_ (.eff root) p.path = some (.layers ls) →
      ∀ (m : MemoMapId) (c : Nat),
        CodeMeans root (resolveLayer root ((Point.spineWalk i p).child 0) m c)
          (layerBuildR root ((Point.spineWalk i p).child 0) m c)
  | .nil, _, i, hi, _, _, _, _, _ => absurd hi (Nat.not_lt_zero i)
  | .cons hd _, p, 0, _, hK, hp, h, m, c => by
    have hh := at_child_of h 0
    show CodeMeans root (resolveLayer root (p.child 0) m c) (layerBuildR root (p.child 0) m c)
    rw [resolveLayer_of_at root hh, layerBuildR_of_at hh]
    exact layerTerm_intro root n hres K hhop hd (p.child 0) m c
      (Nat.le_trans (fuel_child_le p 0) hK) (Nat.lt_of_le_of_lt (weight_child p 0) hp) hh
  | .cons _ tl, p, i + 1, hi, hK, hp, h, m, c =>
    layerTerms_intro root n hres K hhop tl (p.child 1) i (Nat.lt_of_succ_lt_succ hi)
      (Nat.le_trans (fuel_child_le p 1) hK) (Nat.lt_of_le_of_lt (weight_child p 1) hp)
      (at_child_of h 1) m c
termination_by structural ls => ls
end

/-- **A layer's build.** At its point, the frame's `resolveLayer.resolveLayerTerm` and the
term's `denoteLayer` are related, given every program at a lighter point: the structural pass
closed by induction on the fuel a reference's hop spends. -/
theorem layer_intro (root : NativeEff) (n : Nat)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q))
    (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat) (hq : q.weight < n)
    (h : Node.at_ (.eff root) q.path = some (.layer l)) :
    CodeMeans root (resolveLayer.resolveLayerTerm root l q m scope) (denoteLayer root l q m scope) := by
  suffices main : ∀ (K : Nat) (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat),
      q.fuel < K → q.weight < n → Node.at_ (.eff root) q.path = some (.layer l) →
      CodeMeans root (resolveLayer.resolveLayerTerm root l q m scope) (denoteLayer root l q m scope)
    from main (q.fuel + 1) l q m scope (Nat.lt_succ_self _) hq h
  intro K
  induction K with
  | zero => intro l q m scope hK; exact absurd hK (Nat.not_lt_zero _)
  | succ K ih =>
    intro l q m scope hK
    exact layerTerm_intro root n hres K ih l q m scope (Nat.lt_succ_iff.mp hK)

/-- `Effect.provide`'s protocol after its counted step (`internal/layer.ts:15-21`): the scope
made, the layer built into it, the body under the built context, the scope closed. -/
theorem provideLayer_intro (root : NativeEff) (n : Nat)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q))
    (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff) (p : Point)
    (completed : List (FiberId × ExitV)) (hp : p.weight ≤ n) (hpos : p.fuel ≠ 0)
    (h : Node.at_ (.eff root) p.path = some (.eff (.provideLayer l i b))) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeMake FinalizerStrategy.sequential)))
        (.provideLayerWith p))
      (prepareR completed (provideLayerR (fun q m s => denoteLayer root l q m s)
        (fun q => denoteR root b q) (fun q => inlineYield b q) i p)) := by
  have hw : ∀ j, (p.child j).weight < n := fun j =>
    Nat.lt_of_lt_of_le (weight_child_lt p j hpos) hp
  have hl := at_child_of h 0
  have hb := at_child_of h 1
  have hbuild : ∀ (m : MemoMapId) (scope : Nat),
      CodeMeans root (resolveLayer root (p.child 0) m scope)
        (denoteLayer root l (p.child 0) m scope) := by
    intro m scope
    rw [resolveLayer_of_at root hl]
    exact layer_intro root n hres l (p.child 0) m scope (hw 0) hl
  unfold provideLayerR
  rw [prepareR_guardR_bind, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (prepareR completed (storeR (.scopeMake .sequential))) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed' v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some scope =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.provideLayerWith p) (Val.scopeHandle scope)) _
    rw [contAOf_provideLayerWith_scope]
    unfold provideLayerWithK
    rw [h]
    dsimp only
    unfold onExitR
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onExit _ _ _ (prepareR completed' _)
      (fun ex => finalizerR ex (.vis (.inr (.closeScope scope ex)) Effects.Program.pure)) ?_ ?_
      (fun _ _ => rfl) rfl (fun _ => rfl)
    · rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed' _) _ ?_ ?_ rfl (fun _ => rfl)
      · cases i
        · -- `buildWithScope`: the context read, the map forked or created, the build
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _ (prepareR completed' (fiberValR .getContext rfl)) _
            (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
          intro completed'' w
          show CodeMeans root
            (Program.contAOf root (.buildWithScopeFromContext (p.child 0) scope) w) _
          rw [contAOf_buildWithScopeFromContext]
          unfold buildWithScopeK
          simp only [seqR]
          cases hctx : Val.context? w with
          | some ctx =>
            dsimp only
            rw [prepareR_guardR_bind, guardR_bind]
            refine CodeMeans.onSuccess _ _ _ (prepareR completed'' (storeR _)) _
              (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
            intro completed''' u
            simp only [seqR]
            exact withMemoMapThen_intro root (p.child 0) scope _ (fun m => hbuild m scope)
              completed''' u
          | none => exact codeMeans_badShape root
        · -- `local`: a private map, then the build
          simp only [↓reduceIte]
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _ (prepareR completed' (storeR (.memoFork none))) _
            (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
          intro completed'' w
          simp only [seqR]
          exact withMemoMapThen_intro root (p.child 0) scope _ (fun m => hbuild m scope)
            completed'' w
      · intro completed'' built
        show CodeMeans root (Program.contAOf root (.provideLayerBody p) built) _
        rw [contAOf_provideLayerBody]
        unfold provideLayerBodyK
        simp only [seqR]
        cases hd : Env.decode built with
        | some ctx =>
          dsimp only
          rw [resolve_of_at hb, inlineYield_eq_headExit b (p.child 1), headExit_eq_asExit?]
          cases (compileEff b (p.child 1)).asExit? with
          | some exit =>
            simp only [prepareR_pure]
            exact codeMeans_ofExit_pure root exit
          | none =>
            refine (updateContext_intro root _ (Region.program (p.child 1))
              (denoteR root b (p.child 1)) ?_).prepare _
            show CodeMeans root (resolve root (p.child 1)) _
            have hr := hres (p.child 1) (hw 1)
            rw [resolve_of_at hb, denoteAt_of_at hb] at hr
            rw [resolve_of_at hb]
            exact hr
        | none => exact codeMeans_badShape root
    · intro completed'' ex program hprog
      have hp' : Prim.withFiber (EffThunk.closeScope scope ex) = program := Option.some.inj hprog
      rw [← hp']
      refine finalizer_intro root completed'' ex ?_
      exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | none =>
    show CodeMeans root (Program.contAOf root (.provideLayerWith p) v) _
    rw [contAOf_provideLayerWith_other root p v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root


end Effect4.Program.Sched
