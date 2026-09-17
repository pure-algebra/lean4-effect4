import Effect4.Laws.Program.Intro.Fibers

/-!
# Intro.Scope: the scope, layer and service family

The introductions of `scoped`, `acquireRelease`, `provideLayer`, `service` and
`provideService`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! #### 5. Scope, Layers & Decisions family -/

theorem intro_scoped (root : NativeEff) (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (h : Node.at_ (.eff root) p.path = some (.eff (.scoped b))) :
    CodeMeans root (compileEff (.scoped b) p) (denoteR root (.scoped b) p) := by
  rw [compileEff_scoped b hf, denoteR_scoped root b hpos]
  exact CodeMeans.scopedNode p b _ h delivers_pure

theorem intro_acquireRelease (root : NativeEff) (n : Nat) (a r : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) (hle : p.weight ≤ n)
    (hw0 : ∀ i, (p.child i).weight < n)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.acquireRelease a r) p) (denoteR root (.acquireRelease a r) p) := by
  rw [compileEff_acquireRelease a r hf, denoteR_acquireRelease root a r hpos, guardR_bind]
  have hwrel : ∀ (completed : List (FiberId × ExitV)) (a : Val) (ctx : Ctx) (ex : ExitV),
      ((Point.ofCapture (p.capture a ctx) completed).childWith 1 (reifyExitVal ex)).weight < n :=
    fun completed a ctx ex => Nat.lt_of_lt_of_le
      (weight_childWith_lt { p with env := p.env ++ [a], completed } 1 (reifyExitVal ex) hpos) hle
  refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _ ?_ ?_ rfl (fun _ => rfl)
  · exact CodeMeans.actGetContext _ _ rfl (successV root)
  · intro completed v
    show CodeMeans root (Program.contAOf root (.acquireCtx p) v) _
    rw [contAOf_acquireCtx]
    simp only [seqR]
    cases hctx : Val.context? v with
    | some ctx =>
      dsimp only
      refine CodeMeans.actMask _ _ false (.acquireIn p ctx) _ rfl ?_ delivers_pure
      refine acquireIn_intro root p ctx (hres _ (hw0 0)) fun a ex => ?_
      exact foreignRelease_intro root _ ex fun completed' => hres _ (hwrel completed' a ctx ex)
    | none => exact codeMeans_badShape root

theorem intro_provideLayer (root : NativeEff) (n : Nat) (l : LayerTerm NativeOp) (i : Bool)
    (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) (hle : p.weight ≤ n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.provideLayer l i b)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.provideLayer l i b) p) (denoteR root (.provideLayer l i b) p) := by
  rw [compileEff_provideLayer l i b hf, denoteR_provideLayer root l i b hpos]
  unfold suspendR
  refine CodeMeans.suspendBody p _ fun completed => ?_
  rw [suspendBodyAt_provideLayer (q := { p with completed }) hf h, prepareR_constructR]
  exact provideLayer_intro root n hres l i b { p with completed } completed hle hpos h

theorem intro_service (root : NativeEff) (key : ServiceKey) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.service key) p) (denoteR root (.service key) p) := by
  rw [compileEff_service key hf, denoteR_service root key hpos, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _
    (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.serviceLookup key) v) _
  rw [contAOf_serviceLookup]
  unfold serviceLookupK serviceLookupR
  simp only [seqR]
  cases Val.context? v with
  | some ctx =>
    cases hg : ctx.services.getV key with
    | some value => simp only [hg, prepareR_pure]; exact CodeMeans.success _
    | none => simp only [hg, prepareR_pure]; exact CodeMeans.failure _
  | none => exact codeMeans_badShape root

theorem intro_provideService (root : NativeEff) (n : Nat) (key : ServiceKey) (value : Term)
    (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.provideService key value b)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.provideService key value b) p) (denoteR root (.provideService key value b) p) := by
  rw [compileEff_provideService key value b hf, denoteR_provideService root key value b hpos]
  cases evalTerm p.env value with
  | some v =>
    have hb := at_child_of h 0
    refine updateContext_intro root _ (Region.program (p.child 0)) (denoteR root b (p.child 0)) ?_
    show CodeMeans root (resolve root (p.child 0)) _
    rw [resolve_of_at hb]
    exact ih _ (hw0 0) b hb
  | none => exact codeMeans_badShape root

end Effect4.Program.Sched
