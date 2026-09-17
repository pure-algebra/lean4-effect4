import Effect4.Laws.Program.Handles.Term

/-!
# The handle invariant at the compiled alphabet — Compile

Every program emitted by `compileEff` and `resolve` names only handles present in the point's
captured completed exits and environment (`compileEff_keys`, `resolve_keys`).
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## The compile names only what is in scope -/

theorem frontier_keys (p : Point) : nativeKeys (frontier p) ⊆ p.keys := List.Subset.refl _

/-- An exit's handles are the handles of the primitive that embeds it. -/
theorem exitKeys_eq_nativeKeys_ofExit (exit : ExitV) :
    exitKeys exit = nativeKeys (Prim.ofExit exit) := by
  cases exit <;> rfl

theorem badShape_keys : nativeKeys badShape = [] := rfl

section compileArms

/-- The capture registered at a point names the point's handles, the acquired value's and
the context's. -/
theorem Point.capture_keys (p : Point) (a : Val) (ctx : Ctx) :
    (FinName.foreign (p.capture a ctx)).keys ⊆ p.keys ++ a.keys ++ ctx.keys := by
  simp only [FinName.keys, Point.capture, Val.keysList_eq_flatMap, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
  · exact List.Subset.trans p.env_keys_subset
      (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _))
  · exact List.Subset.trans (List.subset_append_right _ _) (List.subset_append_left _ _)
  · exact List.subset_append_right _ _

/-- DI-61. The shared async dispatcher names only handles already captured at the point. -/
theorem asyncRoute_keys (register : NativeOp) (r : Term) (p : Point) :
    nativeKeys (asyncRoute register r p) ⊆ p.keys := by
  unfold asyncRoute
  cases register with
  | external i =>
    cases hv : evalTerm p.env r with
    | none => exact List.nil_subset _
    | some value =>
      simp only [nativeKeys, primKeys, EffName.keys, Option.map_none, Option.getD_none, List.append_nil]
      exact evalTerm_point_keys r p value hv
  | sleep =>
    cases (evalTerm p.env r).bind NativeOp.sleepMillisOf with
    | none => exact List.nil_subset _
    | some n => cases n <;> exact List.nil_subset _
  | deferredAwait =>
    -- the one asynchronous built-in: the awaited cell is a handle the request evaluated to
    simp only [NativeOp.row]
    cases hcell : (evalTerm p.env r).bind NativeOp.awaitCellOf with
    | none => exact List.nil_subset _
    | some cell =>
      obtain ⟨val, hval, hc⟩ := Option.bind_eq_some_iff.mp hcell
      have hmem := awaitCellOf_keys val cell hc
      have hval' := evalTerm_point_keys r p val hval
      have hcellKeys : [Handle.promise cell] ⊆ p.keys := by
        intro key hkey
        obtain rfl := List.mem_singleton.mp hkey
        exact hval' hmem
      sub_tac using hcellKeys
  | scopeMake strategy => cases strategy <;> exact List.nil_subset _
  | _ => exact List.nil_subset _

/-- A capture's point names the capture's environment. -/
theorem Point.ofCapture_keys (c : Capture) : (Point.ofCapture c).keys ⊆ Val.keysList c.env := by
  simp only [Point.keys, Point.ofCapture, List.flatMap_nil, List.nil_append, Val.keysList_eq_flatMap]
  exact List.Subset.refl _

end compileArms

theorem compileEff_keys : ∀ (e : NativeEff) (p : Point), nativeKeys (compileEff e p) ⊆ p.keys
  | .succeed v, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_succeed v hf]
      split
      · next val hval => exact evalTerm_point_keys v p val hval
      · exact List.nil_subset _
  | .fail e, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_fail e hf]; split <;> exact List.nil_subset _
  | .failCause c, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_failCause c hf]; split <;> exact List.nil_subset _
  | .yieldError e, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_yieldError e hf]; split <;> exact List.nil_subset _
  | .sync t, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_sync t hf]; exact List.Subset.refl _
  | .suspend b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_suspend b hf]; exact List.Subset.refl _
  | .perform op r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_perform op r hf]
      split
      · exact asyncRoute_keys _ r p
      · split
        · split
          · next val hval =>
            split
            · next operation hop =>
              exact List.Subset.trans (syncOpOf_keys op val operation hop) (evalTerm_point_keys r p val hval)
            · exact List.nil_subset _
          · exact List.nil_subset _
        · exact asyncRoute_keys op r p
        · exact frontier_keys p
  | .bind a b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_bind a b hf]
      sub_tac using (compileEff_keys a (p.child 0))
  | .gen ss, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_gen ss hf]; exact frontier_keys p
  | .catchCause b h, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_catchCause b h hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .catchIf test b h, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_catchIf test b h hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .matchCause b v c, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_matchCause b v c hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .onExit b f, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_onExit b f hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .exit b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
      · rw [compileEff_exit_frame b hf hx]
        exact compileEff_keys b (p.child 0)
      · -- the folded exit carries the body's own handles
        rw [compileEff_exit_fold b hf hx]
        have hb := compileEff_keys b (p.child 0)
        rw [Prim.asExit?_eq_some _ _ hx, ← exitKeys_eq_nativeKeys_ofExit] at hb
        show (reifyExitVal ex).keys ⊆ p.keys
        rw [Machine.reifyExitVal_keys]
        exact hb
  | .uninterruptible b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_uninterruptible b hf]; exact List.Subset.refl _
  | .interruptible b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_interruptible b hf]; exact List.Subset.refl _
  | .branch t a b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_branch t a b hf]; exact List.Subset.refl _
  | .select s d a b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_select s d a b hf]; exact List.Subset.refl _
  | .whileLoop initial test step b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_whileLoop initial test step b hf]; exact frontier_keys p
  | .yieldNow priority, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_yieldNow priority hf]; exact List.nil_subset _
  | .callback register r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_callback register r hf]
      exact asyncRoute_keys register r p
  | .awaitFiber fiber mode, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_awaitFiber fiber mode hf]
      split
      · next id hid =>
        split
        · next exit hexit =>
          rw [← exitKeys_eq_nativeKeys_ofExit]
          exact p.awaitExit_keys ⟨id⟩ mode exit hexit
        · exact evalTerm_point_keys fiber p (Val.fiber ⟨id⟩) hid
      · exact List.nil_subset _
  | .withFiber a, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · cases a with
      | forkScoped child options =>
        rw [compileEff_forkScoped child options hf]
        sub_tac
      | _ =>
        rw [compileEff_withFiber _ hf (by intro _ _ h; cases h)]
        exact List.Subset.refl _
  | .scoped b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_scoped b hf]; sub_tac
  | .acquireRelease a r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_acquireRelease a r hf]; sub_tac
  -- the join: a suspension at the point, a context read, a region over the evaluated value
  | .provideLayer l i b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_provideLayer l i b hf]; exact List.Subset.refl _
  | .service key, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_service key hf]; sub_tac
  | .provideService key value b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; exact frontier_keys p
    · rw [compileEff_provideService key value b hf]
      split
      · next v hv => sub_tac using (evalTerm_point_keys value p v hv)
      · exact List.nil_subset _

theorem resolve_keys (root : NativeEff) (p : Point) : nativeKeys (resolve root p) ⊆ p.keys := by
  unfold resolve
  split
  · exact compileEff_keys _ _
  · exact List.nil_subset _

end Effect4.Program
