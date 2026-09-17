import Effect4.Laws.Program.Intro.Sequential

/-!
# Intro.Errors: the error-handling family

The introductions of `catchCause`, `catchIf`, `matchCause` and `exit`.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! #### 3. Error Handling family -/

theorem intro_catchCause (root : NativeEff) (n : Nat) (b hd : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.catchCause b hd)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.catchCause b hd) p) (denoteR root (.catchCause b hd) p) := by
  rw [compileEff_catchCause b hd hf, denoteR_catchCause root b hd hpos, guardR_bind]
  refine CodeMeans.onFailure _ _ _ (denoteR root b (p.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
  · exact ih _ (hw0 0) b (at_child_of h 0)
  · intro completed c
    have hb := at_childWith_of (p := { p with completed }) h 1 (.exitErr c)
    show CodeMeans root (resolve root ({ p with completed }.childWith 1 (.exitErr c)))
      (prepareR completed (constructR _))
    rw [resolve_of_at hb]
    simp only [prepareR_constructR, prepareR_denoteR]
    exact ih _ (hwcw completed 1 _) hd hb

theorem intro_catchIf (root : NativeEff) (n : Nat) (test : Term) (b hd : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.catchIf test b hd)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.catchIf test b hd) p) (denoteR root (.catchIf test b hd) p) := by
  rw [compileEff_catchIf test b hd hf, denoteR_catchIf root test b hd hpos, guardR_bind]
  refine CodeMeans.onFailure _ _ _ (denoteR root b (p.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
  · exact ih _ (hw0 0) b (at_child_of h 0)
  · intro completed cause
    simp only [EffName.refreshE, contEOf, h, prepareR_constructR]
    cases caughtErrorValue? p.env test cause with
    | none =>
      simp only [prepareR]
      exact CodeMeans.failure cause
    | some value =>
      simp only
      have hb := at_childWith_of (p := { p with completed }) h 1 value
      rw [resolve_of_at hb]
      simp only [prepareR_denoteR]
      exact ih _ (hwcw completed 1 value) hd hb

theorem intro_matchCause (root : NativeEff) (n : Nat) (b v c : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.matchCause b v c)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.matchCause b v c) p) (denoteR root (.matchCause b v c) p) := by
  rw [compileEff_matchCause b v c hf, denoteR_matchCause root b v c hpos, guardR_bind]
  refine CodeMeans.onBoth _ _ _ _ (denoteR root b (p.child 0)) _ ?_ ?_ ?_ rfl (fun _ => rfl)
  · exact ih _ (hw0 0) b (at_child_of h 0)
  · intro completed x
    have hb := at_childWith_of (p := { p with completed }) h 1 x
    show CodeMeans root (resolve root ({ p with completed }.childWith 1 x))
      (prepareR completed (constructR _))
    rw [resolve_of_at hb]
    simp only [prepareR_constructR, prepareR_denoteR]
    exact ih _ (hwcw completed 1 x) v hb
  · intro completed cause
    have hb := at_childWith_of (p := { p with completed }) h 2 (.exitErr cause)
    show CodeMeans root (resolve root ({ p with completed }.childWith 2 (.exitErr cause)))
      (prepareR completed (constructR _))
    rw [resolve_of_at hb]
    simp only [prepareR_constructR, prepareR_denoteR]
    exact ih _ (hwcw completed 2 _) c hb

theorem intro_exit (root : NativeEff) (n : Nat) (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.exit b)))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.exit b) p) (denoteR root (.exit b) p) := by
  rw [compileEff_exit b hf, denoteR_exit root b p hpos, inlineYield_eq_headExit,
    headExit_eq_asExit?]
  cases (compileEff b (p.child 0)).asExit? with
  | some ex => exact CodeMeans.success _
  | none =>
    show CodeMeans root (Prim.exitFrame _) ((guardR .all _).bind _)
    rw [guardR_bind]
    refine CodeMeans.exitFrame _ _ (denoteR root b (p.child 0))
      (fun ex => .pure (.success (reifyExitVal ex))) ?_ (fun _ _ => CodeMeans.success _) rfl
      (fun _ => rfl)
    exact ih _ (hw0 0) b (at_child_of h 0)

end Effect4.Program.Sched
