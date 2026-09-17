import Effect4.Laws.Program.Intro.Memo

/-!
# Intro.Merge: `mergeAllEffect` for two siblings and for a `mergeAll` spine

The parallel parent, one sequential child per sibling with its build forked into it, the
await and the merge; the fork loop over the spine by the remaining count.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-- `mergeAllEffect` for two siblings (`Layer.ts:1587-1602`): the parallel parent, a sequential
child per sibling with the sibling's build forked into it, the await, the merge. -/
theorem mergeTwo_intro (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat)
    (h0 : ∀ c, CodeMeans root (resolveLayer root (q.child 0) m c) (layerBuildR root (q.child 0) m c))
    (h1 : ∀ c, CodeMeans root (resolveLayer root (q.child 1) m c) (layerBuildR root (q.child 1) m c)) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork child FinalizerStrategy.parallel)))
        (.mergeChildren q m))
      (mergeTwoR q m child) := by
  unfold mergeTwoR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeFork child .parallel)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some parent =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.mergeChildren q m) (Val.scopeHandle parent)) _
    rw [contAOf_mergeChildren_scope]
    dsimp only
    unfold mergeForkR
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (prepareR completed (storeR (.scopeFork parent .sequential))) _
      (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
    intro completed₁ w
    simp only [seqR]
    cases hs0 : Val.scope? w with
    | some c0 =>
      have hw := Val.scope?_exact hs0
      subst hw
      show CodeMeans root
        (Program.contAOf root (.mergeForkOne q 0 m parent []) (Val.scopeHandle c0)) _
      rw [contAOf_mergeForkOne_scope]
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed₁ _) _ ?_ ?_ rfl (fun _ => rfl)
      · exact CodeMeans.actFork _ _ _ (.layerBuild (q.child 0) m c0) _ rfl (h0 c0) (successV root)
      · intro completed₂ f0
        show CodeMeans root (Program.contAOf root (.mergeForkNext q 0 m parent []) f0) _
        simp only [seqR]
        cases hf0 : Val.fiber? f0 with
        | some id0 =>
          have hf := Val.fiber?_exact hf0
          subst hf
          rw [contAOf_mergeForkNext_fiber, if_pos rfl]
          dsimp only
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _
            (prepareR completed₂ (storeR (.scopeFork parent .sequential))) _
            (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
          intro completed₃ w1
          simp only [seqR]
          cases hs1 : Val.scope? w1 with
          | some c1 =>
            have hw1 := Val.scope?_exact hs1
            subst hw1
            show CodeMeans root
              (Program.contAOf root (.mergeForkOne q 1 m parent ([] ++ [id0]))
                (Val.scopeHandle c1)) _
            rw [contAOf_mergeForkOne_scope]
            dsimp only
            rw [prepareR_guardR_bind, guardR_bind]
            refine CodeMeans.onSuccess _ _ _ (prepareR completed₃ _) _ ?_ ?_ rfl (fun _ => rfl)
            · exact CodeMeans.actFork _ _ _ (.layerBuild (q.child 1) m c1) _ rfl (h1 c1)
                (successV root)
            · intro completed₄ f1
              show CodeMeans root
                (Program.contAOf root (.mergeForkNext q 1 m parent ([] ++ [id0])) f1) _
              simp only [seqR]
              cases hf1 : Val.fiber? f1 with
              | some id1 =>
                have hf := Val.fiber?_exact hf1
                subst hf
                rw [contAOf_mergeForkNext_fiber, if_neg Nat.one_ne_zero]
                dsimp only
                rw [prepareR_guardR_bind, guardR_bind]
                refine CodeMeans.onSuccess _ _ _
                  (prepareR completed₄ (fiberValR (.awaitAllFailFast [id0, id1]) rfl)) _
                  (CodeMeans.actAwaitAllFailFast _ _ _ rfl delivers_seqR_pure) ?_ rfl
                  (fun _ => rfl)
                intro completed₅ ex
                show CodeMeans root (Program.contAOf root .mergeContexts ex) _
                rw [contAOf_mergeContexts]
                simp only [seqR]
                unfold mergeContextsK mergeContextsR
                cases contextsOf ex with
                | some ctxs => simp only [prepareR_pure]; exact CodeMeans.success _
                | none =>
                  cases reasonsOfVal ex with
                  | nil => exact codeMeans_badShape root
                  | cons reason rest => simp only [prepareR_pure]; exact CodeMeans.failure _
              | none =>
                show CodeMeans root
                  (Program.contAOf root (.mergeForkNext q 1 m parent ([] ++ [id0])) f1) _
                rw [contAOf_mergeForkNext_other root q 1 m parent _ f1 (Val.fiber?_none hf1)]
                simp only [prepareR_pure]
                exact codeMeans_badShape root
          | none =>
            show CodeMeans root
              (Program.contAOf root (.mergeForkOne q 1 m parent ([] ++ [id0])) w1) _
            rw [contAOf_mergeForkOne_other root q 1 m parent _ w1 (Val.scope?_none hs1)]
            simp only [prepareR_pure]
            exact codeMeans_badShape root
        | none =>
          show CodeMeans root (Program.contAOf root (.mergeForkNext q 0 m parent []) f0) _
          rw [contAOf_mergeForkNext_other root q 0 m parent [] f0 (Val.fiber?_none hf0)]
          simp only [prepareR_pure]
          exact codeMeans_badShape root
    | none =>
      show CodeMeans root (Program.contAOf root (.mergeForkOne q 0 m parent []) w) _
      rw [contAOf_mergeForkOne_other root q 0 m parent [] w (Val.scope?_none hs0)]
      simp only [prepareR_pure]
      exact codeMeans_badShape root
  | none =>
    show CodeMeans root (Program.contAOf root (.mergeChildren q m) v) _
    rw [contAOf_mergeChildren_other root q m v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

/-- The layer at a point, resolved by the term: the node's term, denoted. -/
theorem layerBuildR_of_at {root : NativeEff} {q : Point} {l : LayerTerm NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer l)) (m : MemoMapId) (scope : Nat) :
    layerBuildR root q m scope = denoteLayer root l q m scope := by
  simp [layerBuildR, h]

/-- `mergeAllEffect`'s fork loop for a `mergeAll` (`Layer.ts:1597-1600`, the host rows slice),
from layer `i` with `remaining` layers left and the fibers forked so far: the frame's
`mergeAllForkOne`/`mergeAllForkNext` names and the term's `mergeAllForkR` are related, given
every layer of the spine at its own point. The last step awaits every forked fiber and merges. -/
theorem mergeAllFork_intro (root : NativeEff) (q : Point) (m : MemoMapId) (parent : Nat)
    (count : Nat) (hcount : mergeAllCount root q = count)
    (hi : ∀ i, i < count → ∀ c,
      CodeMeans root (resolveLayer root (q.spineChild i) m c) (layerBuildR root (q.spineChild i) m c)) :
    ∀ (remaining i : Nat) (forked : List FiberId), i + remaining = count →
      CodeMeans root
        (match remaining with
         | 0 => Prim.onSuccess (Prim.withFiber (EffThunk.awaitAllFailFast forked)) .mergeContexts
         | _ + 1 =>
           Prim.onSuccess
             (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
             (.mergeAllForkOne q i m parent forked))
        (mergeAllForkR q m parent remaining i forked)
  | 0, i, forked, _ => by
    show CodeMeans root
      (Prim.onSuccess (Prim.withFiber (EffThunk.awaitAllFailFast forked)) .mergeContexts) _
    simp only [mergeAllForkR]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (fiberValR (.awaitAllFailFast forked) rfl) _
      (CodeMeans.actAwaitAllFailFast _ _ _ rfl delivers_seqR_pure) ?_ rfl (fun _ => rfl)
    intro completed ex
    show CodeMeans root (Program.contAOf root .mergeContexts ex) _
    rw [contAOf_mergeContexts]
    simp only [seqR]
    unfold mergeContextsK mergeContextsR
    cases contextsOf ex with
    | some ctxs => simp only [prepareR_pure]; exact CodeMeans.success _
    | none =>
      cases reasonsOfVal ex with
      | nil => exact codeMeans_badShape root
      | cons reason rest => simp only [prepareR_pure]; exact CodeMeans.failure _
  | remaining + 1, i, forked, hsum => by
    show CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork parent FinalizerStrategy.sequential)))
        (.mergeAllForkOne q i m parent forked)) _
    simp only [mergeAllForkR]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (storeR (.scopeFork parent .sequential)) _
      (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
    intro completed w
    simp only [seqR]
    cases hs : Val.scope? w with
    | some c =>
      have hw := Val.scope?_exact hs
      subst hw
      show CodeMeans root
        (Program.contAOf root (.mergeAllForkOne q i m parent forked) (Val.scopeHandle c)) _
      rw [contAOf_mergeAllForkOne_scope]
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed _) _ ?_ ?_ rfl (fun _ => rfl)
      · exact CodeMeans.actFork _ _ _ (.layerBuild (q.spineChild i) m c) _ rfl
          (hi i (by omega) c) (successV root)
      · intro completed' f
        show CodeMeans root (Program.contAOf root (.mergeAllForkNext q i m parent forked) f) _
        simp only [seqR]
        cases hf : Val.fiber? f with
        | some id =>
          have hf' := Val.fiber?_exact hf
          subst hf'
          rw [contAOf_mergeAllForkNext_fiber, hcount]
          dsimp only
          have ih := mergeAllFork_intro root q m parent count hcount hi remaining (i + 1)
            (forked ++ [id]) (by omega)
          cases remaining with
          | zero =>
            rw [if_neg (by omega)]
            exact ih.prepare completed'
          | succ r =>
            rw [if_pos (by omega)]
            exact ih.prepare completed'
        | none =>
          rw [contAOf_mergeAllForkNext_other root q i m parent forked f (Val.fiber?_none hf)]
          simp only [prepareR_pure]
          exact codeMeans_badShape root
    | none =>
      show CodeMeans root (Program.contAOf root (.mergeAllForkOne q i m parent forked) w) _
      rw [contAOf_mergeAllForkOne_other root q i m parent forked w (Val.scope?_none hs)]
      simp only [prepareR_pure]
      exact codeMeans_badShape root

/-- `mergeAllEffect` for a `mergeAll` (`Layer.ts:1587-1602`, the host rows slice): the parallel
parent, then the fork loop over the spine from layer `0`; no layers is the empty await. -/
theorem mergeAll_intro (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat) (count : Nat)
    (hcount : mergeAllCount root q = count)
    (hi : ∀ i, i < count → ∀ c,
      CodeMeans root (resolveLayer root (q.spineChild i) m c) (layerBuildR root (q.spineChild i) m c)) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork child FinalizerStrategy.parallel)))
        (.mergeAllChildren q m))
      (mergeAllR q m child count) := by
  unfold mergeAllR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeFork child .parallel)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some parent =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.mergeAllChildren q m) (Val.scopeHandle parent)) _
    rw [contAOf_mergeAllChildren_scope, hcount]
    dsimp only
    have ih := mergeAllFork_intro root q m parent count hcount hi count 0 [] (Nat.zero_add _)
    cases count with
    | zero =>
      rw [if_neg (Nat.lt_irrefl 0)]
      exact ih.prepare completed
    | succ c =>
      rw [if_pos (Nat.succ_pos c)]
      exact ih.prepare completed
  | none =>
    show CodeMeans root (Program.contAOf root (.mergeAllChildren q m) v) _
    rw [contAOf_mergeAllChildren_other root q m v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

end Effect4.Program.Sched
