import Effect4.Laws.Program.Intro.Elementary

/-!
# Intro.Sequential: the sequential and loop family

The introductions of `suspend`, `bind`, `gen`, `select`, `iterate` and
`onExit`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! #### 2. Sequential & Loops family -/

theorem intro_suspend (root : NativeEff) (n : Nat) (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hwc : ∀ (c : List (FiberId × ExitV)) (i : Nat),
      (({ p with completed := c } : Point).child i).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.suspend b)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.suspend b) p) (denoteR root (.suspend b) p) := by
  rw [compileEff_suspend b hf, denoteR_suspend root b p hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  have hb := at_child_of (p := { p with completed }) h 0
  show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
  rw [suspendBodyAt_suspend (q := { p with completed }) hf h, resolve_of_at hb]
  simp only [prepareR_constructR, prepareR_denoteR]
  exact ih _ (hwc completed 0) b hb

/-- **An invocation** (decisions row 328): one counted suspension on both sides, then the
definition's body at its point of the root, the request its one variable. The hop spends one
fuel (`weight_redirect_lt`), so the introduction at every lighter point (`hres`) closes it. A step
of `code_intro_aux`; goal G4 of the procedures note. -/
theorem intro_call (root : NativeEff) (n : Nat) (index : Nat) (r : Term) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) (hle : p.weight ≤ n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.perform (.call index) r)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.perform (.call index) r) p)
      (denoteR root (.perform (.call index) r) p) := by
  rw [compileEff_perform (.call index) r hf, denoteR_perform root (.call index) r hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
  rw [suspendBodyAt_call (q := { p with completed }) hf h]
  simp only [prepareR_constructR]
  cases hv : evalTerm p.env r with
  | none => exact codeMeans_badShape root
  | some v =>
    cases hp : defBodyPath root index with
    | none => exact codeMeans_badShape root
    | some path =>
      have hq := hres { ({ p with completed } : Point).redirect path with env := [v] }
        (Nat.lt_of_lt_of_le (weight_redirect_lt p path hpos completed [v]) hle)
      unfold denoteAt at hq
      unfold resolve at hq ⊢
      dsimp only [Point.redirect] at hq ⊢
      cases hb : Node.at_ (Node.eff root) path with
      | none => exact codeMeans_badShape root
      | some node =>
        rw [hb] at hq
        cases node with
        | eff body =>
          rw [prepareR_denoteR]
          exact hq
        | stmts _ => exact codeMeans_badShape root
        | stmt _ => exact codeMeans_badShape root
        | action _ => exact codeMeans_badShape root
        | effs _ => exact codeMeans_badShape root
        | layer _ => exact codeMeans_badShape root
        | layers _ => exact codeMeans_badShape root

/-- **An invocation with programs** (decisions row 340): as an invocation (`intro_call`), with the
sites of the call's programs pushed on the stack. The hop spends one fuel
(`weight_redirect_params_lt`), so the introduction at every lighter point (`hres`) closes it. A
step of `code_intro_aux`. -/
theorem intro_invoke (root : NativeEff) (n : Nat) (index : Nat) (r : Term) (args : Effs NativeOp)
    (p : Point) (k : Nat) (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) (hle : p.weight ≤ n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.invoke index r args)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.invoke index r args) p)
      (denoteR root (.invoke index r args) p) := by
  rw [compileEff_invoke index r args hf, denoteR_invoke (root := root) (p := p) index r args hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
  rw [suspendBodyAt_invoke (q := { p with completed }) hf h]
  simp only [prepareR_constructR]
  cases hv : evalTerm p.env r with
  | none => exact codeMeans_badShape root
  | some v =>
    cases hp : defBodyPath root index with
    | none => exact codeMeans_badShape root
    | some path =>
      have hq := hres
        { ({ p with completed } : Point).redirect path with
          env := [v]
          params := argSitesAt (p.path ++ [0]) p.env args :: p.params }
        (Nat.lt_of_lt_of_le (weight_redirect_params_lt p path hpos completed [v] _) hle)
      unfold denoteAt at hq
      unfold resolve at hq ⊢
      dsimp only [Point.redirect] at hq ⊢
      cases hb : Node.at_ (Node.eff root) path with
      | none => exact codeMeans_badShape root
      | some node =>
        rw [hb] at hq
        cases node with
        | eff body =>
          rw [prepareR_denoteR]
          exact hq
        | stmts _ => exact codeMeans_badShape root
        | stmt _ => exact codeMeans_badShape root
        | action _ => exact codeMeans_badShape root
        | effs _ => exact codeMeans_badShape root
        | layer _ => exact codeMeans_badShape root
        | layers _ => exact codeMeans_badShape root

/-- **A parameter's run** (decisions row 340): one counted suspension on both sides, then the
site of the program that the innermost call passed, its environment extended by the request's
value, at the stack below that call. The hop spends one fuel (`weight_redirect_params_lt`). A
step of `code_intro_aux`. -/
theorem intro_param (root : NativeEff) (n : Nat) (i : Nat) (r : Term) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) (hle : p.weight ≤ n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.perform (.param i) r)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.perform (.param i) r) p)
      (denoteR root (.perform (.param i) r) p) := by
  rw [compileEff_perform (.param i) r hf, denoteR_perform root (.param i) r hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
  rw [suspendBodyAt_param (q := { p with completed }) hf h]
  simp only [prepareR_constructR]
  cases hv : evalTerm p.env r with
  | none => exact codeMeans_badShape root
  | some v =>
    cases hs : p.params with
    | nil => exact codeMeans_badShape root
    | cons top rest =>
      dsimp only
      cases ht : top[i]? with
      | none => exact codeMeans_badShape root
      | some site =>
        have hq := hres
          { ({ p with completed } : Point).redirect site.path with
            env := site.env ++ [v]
            params := rest }
          (Nat.lt_of_lt_of_le (weight_redirect_params_lt p site.path hpos completed _ rest) hle)
        unfold denoteAt at hq
        unfold resolve at hq ⊢
        dsimp only [Point.redirect] at hq ⊢
        cases hb : Node.at_ (Node.eff root) site.path with
        | none => exact codeMeans_badShape root
        | some node =>
          rw [hb] at hq
          cases node with
          | eff body =>
            rw [prepareR_denoteR]
            exact hq
          | stmts _ => exact codeMeans_badShape root
          | stmt _ => exact codeMeans_badShape root
          | action _ => exact codeMeans_badShape root
          | effs _ => exact codeMeans_badShape root
          | layer _ => exact codeMeans_badShape root
          | layers _ => exact codeMeans_badShape root

/-- **A definition block** (decisions row 328): no step of its own on either side, its main
program at child 1. A step of `code_intro_aux`. -/
theorem intro_defs (root : NativeEff) (n : Nat) (decls : List DefDecl) (bodies : Effs NativeOp)
    (main : NativeEff) (p : Point) (k : Nat) (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.defs decls bodies main)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.defs decls bodies main) p)
      (denoteR root (.defs decls bodies main) p) := by
  rw [compileEff_defs decls bodies main hf, denoteR_defs (root := root) (p := p) decls bodies main hpos]
  exact ih _ (hw0 1) main (at_child_of h 1)

theorem intro_bind (root : NativeEff) (n : Nat) (a b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.bind a b)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.bind a b) p) (denoteR root (.bind a b) p) := by
  rw [compileEff_bind a b hf, denoteR_bind root a b p hpos, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (denoteR root a (p.child 0))
    (seqR fun v => constructR fun completed => denoteR root b ({ p with completed }.childWith 1 v))
    ?_ ?_ rfl (fun _ => rfl)
  · exact ih _ (hw0 0) a (at_child_of h 0)
  · intro completed v
    have hb := at_childWith_of (p := { p with completed }) h 1 v
    show CodeMeans root (resolve root ({ p with completed }.childWith 1 v))
      (prepareR completed (constructR _))
    rw [resolve_of_at hb]
    simp only [prepareR_constructR, prepareR_denoteR]
    exact ih _ (hwcw completed 1 v) b hb

theorem intro_gen (root : NativeEff) (ss : Stmts NativeOp) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (h : Node.at_ (.eff root) p.path = some (.eff (.gen ss))) :
    CodeMeans root (compileEff (.gen ss) p) (denoteR root (.gen ss) p) := by
  rw [compileEff_gen ss hf, denoteR_gen root ss p hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  show CodeMeans root (suspendBodyAt root (.body { p with completed }))
    (prepareR completed (.vis (.inr (.gen p)) Effects.Program.pure))
  rw [suspendBodyAt_gen (q := { p with completed }) hf h]
  exact CodeMeans.genEntry p _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ delivers_pure

theorem intro_select (root : NativeEff) (n : Nat) (s : Term) (d : Decision) (a0 a1 : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hwc : ∀ (c : List (FiberId × ExitV)) (i : Nat),
      (({ p with completed := c } : Point).child i).weight < n)
    (hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.select s d a0 a1)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.select s d a0 a1) p) (denoteR root (.select s d a0 a1) p) := by
  rw [compileEff_select s d a0 a1 hf, denoteR_select root s d a0 a1 p hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
  simp only [prepareR_constructR]
  rcases hd : (evalTerm p.env s).bind d.decide with _ | ⟨first, bound⟩
  · rw [suspendBodyAt_select_bad (q := { p with completed }) hf h hd]
    exact codeMeans_badShape root
  · rw [suspendBodyAt_select_of_decide (q := { p with completed }) hf h hd]
    cases first
    · cases bound with
      | none =>
        simp only [Bool.cond_false, Point.childBind]
        have hb := at_child_of (p := { p with completed }) h 1
        simp only [Node.child] at hb
        rw [resolve_of_at hb]
        simp only [prepareR_denoteR]
        exact ih _ (hwc completed 1) a1 hb
      | some v =>
        simp only [Bool.cond_false, Point.childBind]
        have hb := at_childWith_of (p := { p with completed }) h 1 v
        simp only [Node.child] at hb
        rw [resolve_of_at hb]
        simp only [prepareR_denoteR]
        exact ih _ (hwcw completed 1 v) a1 hb
    · cases bound with
      | none =>
        simp only [Bool.cond_true, Point.childBind]
        have hb := at_child_of (p := { p with completed }) h 0
        simp only [Node.child] at hb
        rw [resolve_of_at hb]
        simp only [prepareR_denoteR]
        exact ih _ (hwc completed 0) a0 hb
      | some v =>
        simp only [Bool.cond_true, Point.childBind]
        have hb := at_childWith_of (p := { p with completed }) h 0 v
        simp only [Node.child] at hb
        rw [resolve_of_at hb]
        simp only [prepareR_denoteR]
        exact ih _ (hwcw completed 0 v) a0 hb
/-- `iterate` enters the loop frame: the hooks answer (`loopFinishAt` against `loopFinishRAt`). -/
theorem intro_iterate (root : NativeEff) (c : Option Ty) (i t s r : Term) (b : NativeEff) (p : Point)
    (k : Nat) (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (h : Node.at_ (.eff root) p.path = some (.eff (.iterate c i t s r b))) :
    CodeMeans root (compileEff (.iterate c i t s r b) p)
      (denoteR root (.iterate c i t s r b) p) := by
  rw [compileEff_iterate c i t s r b hf, denoteR_iterate root c i t s r b p hpos]
  refine CodeMeans.suspendBody p _ fun completed => ?_
  show CodeMeans root (suspendBodyAt root (.body { p with completed }))
    (prepareR completed (match evalTerm p.env i with
      | some cursor => .vis (.inr (.loop p cursor)) Effects.Program.pure
      | none => .pure badShapeExit))
  rw [suspendBodyAt_iterate (q := { p with completed }) hf h]
  dsimp only
  rcases hv : evalTerm p.env i with _ | cursor
  · exact codeMeans_badShape root
  · exact CodeMeans.loopEntry p _ cursor _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ delivers_pure

theorem intro_onExit (root : NativeEff) (n : Nat) (b f : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.onExit b f)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.onExit b f) p) (denoteR root (.onExit b f) p) := by
  rw [compileEff_onExit b f hf, denoteR_onExit root b f hpos]
  unfold onExitR
  rw [guardR_bind]
  refine CodeMeans.onExit _ _ _ (denoteR root b (p.child 0))
    (fun ex => finalizerR ex (constructR fun completed =>
      denoteR root f ({ p with completed }.childWith 1 (reifyExitVal ex))))
    ?_ ?_ (fun _ _ => rfl) rfl (fun _ => rfl)
  · exact ih _ (hw0 0) b (at_child_of h 0)
  · intro completed ex program hprog
    have hp' : resolve root ({ p with completed }.childWith 1 (reifyExitVal ex)) = program :=
      Option.some.inj hprog
    rw [← hp']
    refine finalizer_intro root completed ex ?_
    have hb := at_childWith_of (p := { p with completed }) h 1 (reifyExitVal ex)
    rw [resolve_of_at hb]
    simp only [prepareR_constructR, prepareR_denoteR]
    exact ih _ (hwcw completed 1 _) f hb

end Effect4.Program.Sched
