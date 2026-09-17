import Effect4.Laws.Program.Handles.Alphabet

/-!
# The handle invariant at the compiled alphabet — Term

Evaluation of terms within environments and preservation of handle bounds across term evaluations.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## Terms evaluate inside their environment -/

theorem Lit.toVal_keys (l : Lit) (v : Val) (h : l.toVal = some v) : v.keys = [] := by
  cases l with
  | unit => cases h; rfl
  | nat n => cases h; rfl
  | bool b => cases h; rfl
  | str s => cases h; rfl

/-- Cause-tag queries construct only a Boolean, never a new handle. -/
theorem queryTag_keys (tag : ReasonTag) (input output : Val)
    (h : queryTag tag input = some output) : output.keys = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.map_eq_some_iff.mp h
  cases houtput
  rfl

/-- A cause-error query wraps only S2's closed, handle-free error image. -/
theorem queryError_keys (input output : Val) (h : queryError input = some output) :
    output.keys = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.bind_eq_some_iff.mp h
  cases hfound : (reasons.findSome? Reason.error?).bind valOfErr with
  | none =>
    simp only [hfound] at houtput
    cases houtput
    rfl
  | some value =>
    simp only [hfound] at houtput
    cases houtput
    change value.keys = []
    obtain ⟨error, _, hvalue⟩ := Option.bind_eq_some_iff.mp hfound
    exact valOfErr_keys error value hvalue

theorem nativeAtom_keys (atom : String) (vs : List Val) (v : Val) (h : nativeAtom atom vs = some v) :
    v.keys ⊆ vs.flatMap Val.keys := by
  unfold nativeAtom at h
  obtain ⟨named, _, h⟩ := Option.bind_eq_some_iff.mp h
  unfold NativeAtom.eval at h
  -- one goal per row of `NativeAtom.eval`, in the table's order: `strings` is row 12 and the
  -- four cause queries rows 13–16; every other answering row is a scalar or a rearrangement
  -- of its arguments, and every refusing row is `none`
  split at h
  case h_12 =>
    unfold stringsAtom at h
    split at h
    · cases h
      rw [Val.keys_list]
      exact List.Subset.refl _
    · cases h
  case h_13 => rw [queryTag_keys _ _ _ h]; exact List.nil_subset _
  case h_14 => rw [queryError_keys _ _ h]; exact List.nil_subset _
  case h_15 => rw [queryTag_keys _ _ _ h]; exact List.nil_subset _
  case h_16 => rw [queryTag_keys _ _ _ h]; exact List.nil_subset _
  all_goals cases h
  all_goals sub_tac norm [Val.tuple]

theorem flatMap_subset_of_subset {α : Type} {f : α → List Handle} {l l' : List α} (h : l' ⊆ l) :
    l'.flatMap f ⊆ l.flatMap f := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h ha, hx⟩

mutual
theorem evalTerm_keys (t : Term) (env : List Val) (v : Val) (h : evalTerm env t = some v) :
    v.keys ⊆ env.flatMap Val.keys := by
  cases t with
  | var i =>
    have h' : env[i]? = some v := h
    exact fun x hx => List.mem_flatMap.mpr ⟨v, List.mem_of_getElem? h', hx⟩
  | lit l =>
    have h' : l.toVal = some v := h
    rw [Lit.toVal_keys l v h']
    exact List.nil_subset _
  | app atom args =>
    rw [evalTerm_app] at h
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h
    exact List.Subset.trans (nativeAtom_keys atom vs v hv) (evalTerms_keys args env vs hvs)
termination_by structural t
theorem evalTerms_keys (ts : Terms) (env : List Val) (vs : List Val) (h : evalTerms env ts = some vs) :
    vs.flatMap Val.keys ⊆ env.flatMap Val.keys := by
  cases ts with
  | nil =>
    have h' : some ([] : List Val) = some vs := h
    cases h'
    exact List.nil_subset _
  | cons head tail =>
    rw [evalTerms_cons] at h
    obtain ⟨v1, hv1, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    cases hcons
    rw [List.flatMap_cons]
    exact List.append_subset.mpr ⟨evalTerm_keys head env v1 hv1, evalTerms_keys tail env rest hrest⟩
termination_by structural ts
end

theorem evalTerm_point_keys (t : Term) (p : Point) (v : Val) (h : evalTerm p.env t = some v) :
    v.keys ⊆ p.keys :=
  List.Subset.trans (evalTerm_keys t p.env v h) p.env_keys_subset

theorem exitOfVal_keys (v : Val) (e : ExitV) (h : exitOfVal v = some e) : exitKeys e ⊆ v.keys := by
  rw [exitImage.ofVal_exact h]
  cases e with
  | success x =>
    show x.keys ⊆ Val.keys (Val.exitOk x)
    rw [Val.keys_exitOk]
    exact List.Subset.refl _
  | failure c => exact List.nil_subset _

theorem awaitCellOf_keys (v : Val) (cell : DeferredKey) (h : NativeOp.awaitCellOf v = some cell) :
    Handle.promise cell ∈ v.keys := by
  unfold NativeOp.awaitCellOf at h
  split at h
  · injection h with h
    subst h
    simp only [Val.keys, Handle.ofCode_promise, Option.toList, List.mem_singleton]
  · exact nomatch h

theorem syncOpOf_keys (op : NativeOp) (v : Val) (o : SyncOp) (h : NativeOp.syncOpOf op v = some o) :
    o.keys ⊆ v.keys := by
  unfold NativeOp.syncOpOf at h
  split at h <;> cases h <;> sub_tac

theorem tuple?_keys (v : Val) : ∀ vs, Val.tuple? v = some vs → vs.flatMap Val.keys ⊆ v.keys := by
  intro vs h
  rw [Val.tuple?_exact h, Val.tuple, Val.keys_list]
  exact List.Subset.refl _

theorem mapM_fiber_keys (g : Val → Option FiberId) (hg : ∀ v id, g v = some id → Handle.fiber id ∈ v.keys) :
    ∀ (vs : List Val) (ids : List FiberId), vs.mapM g = some ids → ids.map Handle.fiber ⊆ vs.flatMap Val.keys
  | [], ids, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact List.nil_subset _
  | v :: vs, ids, h => by
    simp only [List.mapM_cons, bind, pure] at h
    obtain ⟨id, hid, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    simp only [Option.some.injEq] at hcons
    subst hcons
    simp only [List.map_cons, List.flatMap_cons]
    exact List.cons_subset.mpr ⟨List.mem_append_left _ (hg v id hid),
      List.Subset.trans (mapM_fiber_keys g hg vs rest hrest) (List.subset_append_right _ _)⟩

end Effect4.Program
