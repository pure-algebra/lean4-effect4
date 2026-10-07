import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics
import Effect4.Program.Typing
import Effect4.Program.Native
import Effect4.Program.SigApp
import Aesop

/-!
# Laws.Program.Template — the row-template calculus (decisions rows 42 and 303)

`Ty.instantiate` (`Program/Ty.lean`) with its laws. Instantiation carries a widening to every
template (`cata_admits_instantiate`). On a closed template instantiation is the identity
(`instantiate_closed`), so a closed row types exactly as it did before the templates
(`rowTy_closed`, `rowTy_closed_some`). `closed` survives `normalize` (`closed_normalize`). The
`Ref` and `Deferred` rows are templates over their type parameters (the state plan's T3a), so the
native rows' profile holds at every operation whose own type arguments are closed
(`NativeOp.row_templateAdmissible`, `NativeOp.row_wellScoped`). An instance's normal form reads
only its bindings' normal forms (`Ty.normalize_instantiate_congr`).
-/

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

namespace Ty

theorem closed_members (t : Ty) (h : closed t = true) : ∀ x ∈ members t, closed x = true := by
  induction t <;> aesop (add norm simp [closed, members])

theorem closed_factors (t : Ty) (h : closed t = true) : ∀ x ∈ factors t, closed x = true := by
  cases t <;> aesop (add norm simp [factors, closed, members], safe forward closed_members)

theorem closed_ofMembers (xs : List Ty) (h : ∀ x ∈ xs, closed x = true) :
    closed (ofMembers xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases xs <;> aesop (add norm simp [ofMembers, closed])

/-- A product of closed factors normalizes to a closed type (the product case, shared with the
pair tuple). -/
theorem closed_productRow (a b : Ty) (ha : closed a = true) (hb : closed b = true) :
    closed (ofMembers (normalizeRow (productMembers a b)).elems) = true := by
  aesop (add norm simp [closed, productMembers, mem_normalizeRow],
    safe apply closed_ofMembers, safe forward closed_factors)

/-- A tuple of closed items normalizes to a closed type. -/
theorem closed_normTuple : ∀ (xs : List Ty), (∀ t ∈ xs, closed t = true) → closed (normTuple xs) = true
  | [a, b], h => closed_productRow a b (h a List.mem_cons_self)
      (h b (List.mem_cons_of_mem _ List.mem_cons_self))
  | [], _ => rfl
  | [a], h => by
    simp only [normTuple, closed, closedItems_eq_all, List.all_cons, List.all_nil,
      h a List.mem_cons_self, Bool.and_true]
  | _ :: _ :: _ :: _, h => by
    simp only [normTuple, closed, closedItems_eq_all, List.all_eq_true]
    exact h

/-- A reference at closed arguments normalizes to a closed type. -/
theorem closed_normApp (n : String) :
    ∀ (xs : List Ty), (∀ t ∈ xs, closed t = true) → closed (normApp n xs) = true
  | [], _ => rfl
  | _ :: _, h => by
    simp only [normApp, closed, closedItems_eq_all, List.all_eq_true]
    exact h

theorem closed_normalize (t : Ty) (h : closed t = true) : closed (normalize t) = true := by
  induction t with
  | prod a b iha ihb =>
    aesop (add norm simp [closed, normalize, productMembers, mem_normalizeRow],
      safe apply closed_ofMembers, safe forward closed_factors)
  | union a b iha ihb =>
    aesop (add norm simp [closed, normalize, mem_normalizeRow],
      safe apply closed_ofMembers, safe forward closed_members)
  | record fs ih =>
    simp only [closed, closedFields_eq_all, List.all_eq_true] at h ⊢
    rw [normalize_record]
    simp only [closed, closedFields_eq_all, List.all_eq_true]
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q (mem_canon hq) (h q (mem_canon hq))
  | tuple ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    rw [normalize, normalizeItems_eq_map]
    exact closed_normTuple _ fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ih u hu (h u hu)
  | app n ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    rw [normalize, normalizeItems_eq_map]
    exact closed_normApp n _ fun t ht => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact ih u hu (h u hu)
  | _ => aesop (add norm simp [closed, normalize])

theorem instantiate_closed (σ : Subst) (t : Ty) (h : closed t = true) : instantiate σ t = t := by
  induction t with
  | record fs ih =>
    simp only [closed, closedFields_eq_all, List.all_eq_true] at h
    rw [instantiate, instantiateFields_eq_map]
    congr 1
    conv => rhs; rw [← List.map_id fs]
    apply List.map_congr_left
    intro p hp
    rw [ih p hp (h p hp)]
    rfl
  | tuple ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    rw [instantiate, instantiateItems_eq_map]
    congr 1
    conv => rhs; rw [← List.map_id ts]
    exact List.map_congr_left fun t ht => ih t ht (h t ht)
  | app n ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    rw [instantiate, instantiateItems_eq_map]
    congr 1
    conv => rhs; rw [← List.map_id ts]
    exact List.map_congr_left fun t ht => ih t ht (h t ht)
  | _ => aesop (add norm simp [closed, instantiate])

/-- The field a closed record's lookup finds is closed. -/
theorem closed_of_lookup {fs : List (String × Bool × Ty)} {n : String} {o : Bool} {ty : Ty}
    (hl : fs.lookup n = some (o, ty)) (h : closedFields fs = true) : closed ty = true := by
  induction fs with
  | nil => cases hl
  | cons p fs ih =>
    obtain ⟨m, o', t'⟩ := p
    have hc := Bool.and_eq_true_iff.mp h
    simp only [List.lookup] at hl
    split at hl
    · cases hl
      exact hc.1
    · exact ih hl hc.2

/-! ### Widening substitutions
 
Instantiation carries a widening to every template, as a condition on the admission algebra — every child
read forward (`AdmitsMono`), not an argument about `hasTy`. It is not the order's own condition
(`AdmitsSub`): an invariant position there only promises to keep EQUIVALENT admissions, while a
widening moves its child one way; membership reads every position forward at the value level
(a handle ignores its argument, decisions row 44), so the admission fold satisfies both. -/

/-- `σ'` admits at every parameter at least what `σ` admits there. -/
def Widens (σ σ' : Subst) : Prop :=
  ∀ i v al, Val.hasTy v (instantiate σ (.var i)) al = true →
    Val.hasTy v (instantiate σ' (.var i)) al = true

theorem Widens.refl (σ : Subst) : Widens σ σ := fun _ _ _ h => h

theorem Widens.trans {σ₁ σ₂ σ₃ : Subst} (h₁ : Widens σ₁ σ₂) (h₂ : Widens σ₂ σ₃) :
    Widens σ₁ σ₃ := fun i v al h => h₂ i v al (h₁ i v al h)

/-- A widening read off the bindings: every binding of `σ` has one in `σ'` above it. An
unbound parameter instantiates to `never`, so it needs nothing. -/
theorem Widens.of_lookup {σ σ' : Subst}
    (h : ∀ j u, σ.lookup j = some u → ∃ u', σ'.lookup j = some u' ∧ sub u u' = true) :
    Widens σ σ' := by
  intro j v al hv
  simp only [instantiate] at hv ⊢
  cases hj : σ.lookup j with
  | none => simp only [hj, Option.getD_none, Val.hasTy, Bool.false_eq_true] at hv
  | some u =>
    obtain ⟨u', hj', hsub⟩ := h j u hj
    simp only [hj, Option.getD_some] at hv
    simp only [hj', Option.getD_some]
    exact hasTy_sub u u' v al hsub hv

/-- Instantiation is monotone in the bindings, for any admission algebra monotone in every child:
bindings that admit more make every template admit more. -/
theorem cata_admits_instantiate {alg : TyAlgebra AdmCarrier} (h : AdmitsMono alg) {σ σ' : Subst}
    (hσ : ∀ i, Adm.le (cata_ty alg (instantiate σ (.var i))).2
      (cata_ty alg (instantiate σ' (.var i))).2)
    (t : Ty) : Adm.le (cata_ty alg (instantiate σ t)).2 (cata_ty alg (instantiate σ' t)).2 := by
  induction t with
  | var i => exact hσ i
  | option t ih => simp only [instantiate, cata_ty]; exact h.option _ _ ih
  | list t ih => simp only [instantiate, cata_ty]; exact h.list _ _ ih
  | causeOf t ih => simp only [instantiate, cata_ty]; exact h.causeOf _ _ ih
  | refOf t ih => simp only [instantiate, cata_ty]; exact h.refOf _ _ ih
  | prod a b iha ihb => simp only [instantiate, cata_ty]; exact h.prod _ _ _ _ iha ihb
  | except a b iha ihb => simp only [instantiate, cata_ty]; exact h.except _ _ _ _ iha ihb
  | exitOf a b iha ihb => simp only [instantiate, cata_ty]; exact h.exitOf _ _ _ _ iha ihb
  | fiberOf a b iha ihb => simp only [instantiate, cata_ty]; exact h.fiberOf _ _ _ _ iha ihb
  | deferredOf a b iha ihb => simp only [instantiate, cata_ty]; exact h.deferredOf _ _ _ _ iha ihb
  | union a b iha ihb => simp only [instantiate, cata_ty]; exact h.union _ _ _ _ iha ihb
  | map a b iha ihb => simp only [instantiate, cata_ty]; exact h.map _ _ _ _ iha ihb
  | record fs ih =>
    simp only [instantiate, cata_ty_record, instantiateFields_eq_map, List.map_map]
    refine h.record _ _ ?_ ?_
    · simp only [List.map_map]
      rfl
    · intro p q hpq
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨f1, f2⟩, hf, hpq⟩ := hpq
      have heq : f1 = f2 := Ty.mem_zip_self hf
      subst heq
      cases hpq
      exact ih f1 (List.of_mem_zip hf).1
  | tuple ts ih =>
    simp only [instantiate, cata_ty_tuple, instantiateItems_eq_map, List.map_map]
    refine h.tuple _ _ (by rw [List.length_map, List.length_map]) ?_
    intro p q hpq
    rw [List.zip_map, List.mem_map] at hpq
    obtain ⟨⟨t1, t2⟩, ht, hpq⟩ := hpq
    have heq : t1 = t2 := Ty.mem_zip_self ht
    subst heq
    cases hpq
    exact ih t1 (List.of_mem_zip ht).1
  | app n ts ih =>
    simp only [instantiate, cata_ty_app, instantiateItems_eq_map, List.map_map]
    refine h.app _ _ _ (by rw [List.length_map, List.length_map]) ?_
    intro p q hpq
    rw [List.zip_map, List.mem_map] at hpq
    obtain ⟨⟨t1, t2⟩, ht, hpq⟩ := hpq
    have heq : t1 = t2 := Ty.mem_zip_self ht
    subst heq
    cases hpq
    exact ih t1 (List.of_mem_zip ht).1
  -- every other head is closed: both instances are the node itself
  | _ => simp only [instantiate]; exact Adm.le_refl _

/-- `cata_admits_instantiate` for the admission fold of this tree. -/
theorem hasTy_instantiate_widens {σ σ' : Subst} (hw : Widens σ σ') (t : Ty)
    (v : Effect4.Machine.Val) (al : List String) (hv : Val.hasTy v (instantiate σ t) al = true) :
    Val.hasTy v (instantiate σ' t) al = true := by
  rw [Val.hasTy.eq_cata v (instantiate σ t) al] at hv
  rw [Val.hasTy.eq_cata v (instantiate σ' t) al]
  refine cata_admits_instantiate Val.hasTy_admitsMono (fun i w bl hw' => ?_) t v al hv
  rw [← Val.hasTy.eq_cata w (instantiate σ (.var i)) bl] at hw'
  rw [← Val.hasTy.eq_cata w (instantiate σ' (.var i)) bl]
  exact hw i w bl hw'

end Ty


/-- A closed template offers no candidate for matching by bounds. -/
theorem Bounds.cands_closed (v : Ty.Variance) (t r : Ty) (h : t.closed = true) :
    Bounds.cands v t r = [] := by
  revert h
  induction v, t, r using Bounds.cands.induct_unfolding
      (motive_2 := fun _ _ _ ts _ result => Ty.closedItems ts = true → result = [])
      (motive_3 := fun _ ts _ result => Ty.closedItems ts = true → result = [])
      (motive_4 := fun _ fs _ result => Ty.closedFields fs = true → result = [])
  case case1 => intro h; cases h
  case case2 ih | case3 ih | case4 ih | case5 ih => exact ih
  case case6 ih₁ ih₂ | case7 ih₁ ih₂ | case8 ih₁ ih₂ | case9 ih₁ ih₂ | case10 ih₁ ih₂
  | case11 ih₁ ih₂ | case12 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    rw [ih₁ hc.1, ih₂ hc.2]
    rfl
  case case13 ih | case14 ih | case15 ih => exact ih
  case case16 => intro _; rfl
  case case17 ih₁ ih₂ =>
    intro h
    rw [ih₁ h, ih₂ h]
    rfl
  case case18 => intro _; rfl
  case case19 => rfl
  case case20 ih h => exact ih h
  case case21 hl ih₁ ih₂ h =>
    rw [ih₁ (Ty.closed_of_lookup hl h), ih₂ h]
    rfl
  case case22 ih₁ ih₂ h =>
    have hc := Bool.and_eq_true_iff.mp h
    rw [Bounds.candsArgs, ih₁ hc.1, ih₂ hc.2]
    rfl
  case case23 =>
    rw [Bounds.candsArgs]
    assumption
  case case24 ih₁ ih₂ h =>
    have hc := Bool.and_eq_true_iff.mp h
    rw [Bounds.candsItems, ih₁ hc.1, ih₂ hc.2]
    rfl
  case case25 =>
    rw [Bounds.candsItems]
    assumption

/-- On a closed template the match by bounds is subsumption of the normal forms, and the seed. -/
theorem Bounds.matchB_closed (seed : Ty.Subst) (t r : Ty) (h : t.closed = true) :
    Bounds.matchB seed t r = if Ty.sub r.normalize t.normalize then some seed else none := by
  dsimp only [Bounds.matchB]
  rw [Bounds.cands_closed .co t r h]
  dsimp only [Bounds.solve, List.filterMap_nil]
  simp only [List.append_nil, Ty.instantiate_closed seed t h]

/-- On a closed template the guard holds, so the guarded match is the match by bounds: the
subsumption of the normal forms, and the seed. A step of `rowTy_closed`. -/
theorem Bounds.matchTerm_closed (seed : Ty.Subst) (t r : Ty) (h : t.closed = true) :
    Bounds.matchTerm seed t r = if Ty.sub r.normalize t.normalize then some seed else none := by
  have guard : Bounds.termGuard seed t r = true := by
    simp only [Bounds.termGuard, Bounds.cands_closed .co t r h, List.all_nil]
  rw [Bounds.matchTerm, if_pos guard, Bounds.matchB_closed seed t r h]

theorem Bounds.solve_lookup_of_mem {seed : Ty.Subst} {cs : List Bounds.Cand} {j : Nat} {u : Ty}
    (h : seed.lookup j = some u) : (Bounds.solve seed cs).lookup j = some u := by
  dsimp only [Bounds.solve]
  rw [List.lookup_append, h, Option.some_or]

theorem Bounds.matchB_keeps {seed σ : Ty.Subst} {template request : Ty}
    (h : Bounds.matchB seed template request = some σ) :
    ∀ j u, seed.lookup j = some u → σ.lookup j = some u := by
  dsimp only [Bounds.matchB] at h
  split at h
  · cases h
    intro j u hj
    exact Bounds.solve_lookup_of_mem hj
  · contradiction

theorem Bounds.matchB_widens {seed σ : Ty.Subst} {template request : Ty}
    (h : Bounds.matchB seed template request = some σ) :
    Ty.Widens seed σ := by
  apply Ty.Widens.of_lookup
  intro j u hj
  exact ⟨u, Bounds.matchB_keeps h j u hj, Ty.sub_refl u⟩

/-- **The match of a binder term answers only where the match by bounds answers**, with the same
bindings: the interim guard refuses, and it binds nothing. So each law of `Bounds.matchB` holds
of a binder term's match. A step of `bindTerm_some_ok`, its consumer. It does not say where
the guard holds: `Bounds.termGuard` decides that. -/
theorem Bounds.matchB_of_matchTerm {seed σ : Ty.Subst} {template request : Ty}
    (h : Bounds.matchTerm seed template request = some σ) :
    Bounds.matchB seed template request = some σ := by
  unfold Bounds.matchTerm at h
  split at h
  · exact h
  · exact nomatch h

/-- A binder term binds by its result template's match at its own type (`bindTerm`). A step of
`bindTerm_widens` and of the row lemmas below. -/
theorem bindTerm_some_ok {σ σ' : Ty.Subst} {u : TermUse} (h : bindTerm σ (some u) = .ok σ') :
    ∃ r, u.typeAt (TermUse.instParam u.param σ) = some r ∧
      Bounds.matchB σ u.result.normalize r = some σ' := by
  simp only [bindTerm] at h
  split at h
  · exact nomatch h
  · rename_i r hr
    split at h
    · rename_i σ'' hm
      cases h
      exact ⟨r, hr, Bounds.matchB_of_matchTerm hm⟩
    · exact nomatch h

/-- A binder term only widens the request's bindings: its result template's match widens its
seed (`Bounds.matchB_widens`), and no term binds nothing. A step of `rowTy_fits`
(`Typed/Denotation.lean`), the inversion of the row rule at a term use. -/
theorem bindTerm_widens {σ σ' : Ty.Subst} {use : Option TermUse} (h : bindTerm σ use = .ok σ') :
    Ty.Widens σ σ' := by
  cases use with
  | none => cases h; exact Ty.Widens.refl σ
  | some u =>
    obtain ⟨_, _, hm⟩ := bindTerm_some_ok h
    exact Bounds.matchB_widens hm

/-- **A binder term keeps the request's bindings, unchanged**: its result template's match keeps
its seed (`Bounds.matchB_keeps`), and no term binds nothing. So the element type `A` the
request bound is the one the row's columns are instantiated at; the term adds `Ref.modify`'s `B`
and moves nothing. A step of `syncRow_typed` (`Typed/Denotation.lean`) at the term rows. -/
theorem bindTerm_keeps {σ σ' : Ty.Subst} {use : Option TermUse} (h : bindTerm σ use = .ok σ') :
    ∀ j u, σ.lookup j = some u → σ'.lookup j = some u := by
  cases use with
  | none => cases h; exact fun _ _ hj => hj
  | some u =>
    obtain ⟨_, _, hm⟩ := bindTerm_some_ok h
    exact Bounds.matchB_keeps hm

/-- A binder term's refusal is its own: no term use refuses as the request. A step of
`checkRow_request_iff`. -/
theorem bindTerm_ne_requestNotSubtype (σ : Ty.Subst) (use : Option TermUse) :
    bindTerm σ use ≠ .error .requestNotSubtype := by
  intro h
  cases use with
  | none => exact nomatch h
  | some u =>
    simp only [bindTerm] at h
    split at h
    · exact nomatch h
    · split at h <;> exact nomatch h

/-- A binder term's refusal is its own: no term use refuses as an instantiated column. A step
of `checkRow_formation_iff`. -/
theorem bindTerm_ne_formation (σ : Ty.Subst) (use : Option TermUse) (why : FormationRefusal) :
    bindTerm σ use ≠ .error (.formation why) := by
  intro h
  cases use with
  | none => exact nomatch h
  | some u =>
    simp only [bindTerm] at h
    split at h
    · exact nomatch h
    · split at h <;> exact nomatch h

/-- A closed, raw formed row types by subsumption and its own columns.
The formation premise is required by rows 192 and 193 even on closed rows. -/
theorem rowTy_closed (row : Row) (r : Ty) (hreq : row.request.closed = true)
    (hans : row.answer.closed = true) (herr : row.error.closed = true)
    (formed : Formation.Formed (Formation.instantiatedSites row [])) :
    rowTy row r =
      if Ty.sub r.normalize row.request.normalize then
        some ⟨row.answer.normalize, row.error.normalize, Requirement.ofList row.requires⟩
      else none := by
  have hformed := (Formation.check_eq_none_iff _).mpr formed
  cases hsub : Ty.sub r.normalize row.request.normalize with
  | false =>
    simp only [rowTy, checkRow, Bounds.matchTerm_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, Bool.false_eq_true, ↓reduceIte, Except.toOption]
  | true =>
    simp only [rowTy, checkRow, Bounds.matchTerm_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, ↓reduceIte, bindTerm_none, hformed, Except.toOption,
      Ty.instantiate_closed _ _ hans, Ty.instantiate_closed _ _ herr]

/-- A successful closed-row match still exposes subsumption and its own columns.
Success itself discharges the new formation guard, so callers need no added premise. -/
theorem rowTy_closed_some {row : Row} {r : Ty} {t : EffTy} (hreq : row.request.closed = true)
    (hans : row.answer.closed = true) (herr : row.error.closed = true)
    (h : rowTy row r = some t) :
    Ty.sub r.normalize row.request.normalize = true ∧
      t = ⟨row.answer.normalize, row.error.normalize, Requirement.ofList row.requires⟩ := by
  rw [rowTy_eq_some_iff] at h
  cases hsub : Ty.sub r.normalize row.request.normalize with
  | false =>
    simp only [checkRow, Bounds.matchTerm_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  | true =>
    simp only [checkRow, Bounds.matchTerm_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, ↓reduceIte, bindTerm_none] at h
    split at h
    · cases h
    · simp only [Ty.instantiate_closed _ _ hans, Ty.instantiate_closed _ _ herr,
        Except.ok.injEq] at h
      exact ⟨rfl, h.symm⟩

/-- `instantiated-formation`: a successful row use retains the actual bindings, the request's
and then the binder term's (`bindTerm`), and strict formation of every substituted column.
Typing consumes this through `rowTy`. This is a static property; it makes no host reply or
execution claim. -/
theorem rowTy_instantiated_formed {row : Row} {request : Ty} {use : Option TermUse} {ty : EffTy}
    (accepted : rowTy row request use = some ty) :
    ∃ σ bindings, Bounds.matchTerm [] row.request.normalize request.normalize = some σ ∧
      bindTerm σ use = .ok bindings ∧
      Formation.Formed (Formation.instantiatedSites row bindings) := by
  rw [rowTy_eq_some_iff] at accepted
  unfold checkRow at accepted
  split at accepted
  · cases accepted
  · rename_i σ matched
    split at accepted
    · cases accepted
    · rename_i bindings bound
      split at accepted
      · cases accepted
      · rename_i formed
        exact ⟨σ, bindings, matched, bound, (Formation.check_eq_none_iff _).mp formed⟩

/-- The precise diagnostic part of `instantiated-formation`: this refusal names
an actual failed column check after a successful template match and term binding. -/
theorem checkRow_formation_iff (row : Row) (request : Ty) (use : Option TermUse)
    (why : FormationRefusal) :
    checkRow row request use = .error (.formation why) ↔
      ∃ σ bindings, Bounds.matchTerm [] row.request.normalize request.normalize = some σ ∧
        bindTerm σ use = .ok bindings ∧
        Formation.check (Formation.instantiatedSites row bindings) = some why := by
  constructor
  · intro refused
    unfold checkRow at refused
    split at refused
    · cases refused
    · rename_i σ matched
      split at refused
      · rename_i failure bound
        have same : failure = .formation why := Except.error.inj refused
        subst same
        exact absurd bound (bindTerm_ne_formation σ use why)
      · rename_i bindings bound
        split at refused
        · rename_i actual failed
          have same : actual = why := RowTypingRefusal.formation.inj (Except.error.inj refused)
          subst same
          exact ⟨σ, bindings, matched, bound, failed⟩
        · cases refused
  · rintro ⟨σ, bindings, matched, bound, failed⟩
    simp only [checkRow, matched, bound, failed]

/-- Request mismatch retains its exact meaning and precedence. Neither the binder term nor the
formation branch can be reported as a subtype mismatch by the shared row checker. -/
theorem checkRow_request_iff (row : Row) (request : Ty) (use : Option TermUse) :
    checkRow row request use = .error .requestNotSubtype ↔
      Bounds.matchTerm [] row.request.normalize request.normalize = none := by
  cases matched : Bounds.matchTerm [] row.request.normalize request.normalize with
  | none => simp only [checkRow, matched]
  | some σ =>
    simp only [checkRow, matched, reduceCtorEq, iff_false]
    cases bound : bindTerm σ use with
    | error why =>
      intro refused
      have same : why = .requestNotSubtype := Except.error.inj refused
      subst same
      exact bindTerm_ne_requestNotSubtype σ use bound
    | ok bindings =>
      dsimp only
      split <;> simp only [Except.error.injEq, reduceCtorEq, not_false_eq_true]

/-! ## What a row's template may say, and what the guard buys (plan 1.8)

Three properties of the calculus, stated as theorems rather than left in prose.

`templateAdmissible` and `Row.wellScoped` are the two shapes a row's template must have for
a match to mean anything. Every native row of this cut is admissible, and every native row
whose operation carries no term is well scoped. A term row's answer may also name a parameter
its term's result template binds, `Ref.modify`'s `B`: the checker binds it from the term's type
(`bindTerm`), so the native profile reads the result template beside the request
(`NativeOp.row_wellScoped`). A host row carries no term, and the signature's admission keeps
`Row.wellScoped` for it. `sub_sound` and
`sub_not_complete` are the two halves of what the guard is worth: the order NEVER admits a
value the target would refuse, and it DOES refuse pairs whose value sets agree. A checker
built on it can lose a program, never mistype one.

The predicates are defined in the core, because the signature's admission reads them
(`rowChecks`, `Program/SigApp.lean`): `Ty.varsOf` and `Ty.templateAdmissible` beside the template
calculus (`Program/Ty.lean`), `Row.wellScoped` beside the row checks (`Program/SigApp.lean`). -/

namespace Ty

/-- The list equation used by `templateAdmissible_of_closed` for row admission. -/
theorem templateAdmissibleFields_eq_all (fs : List (String × Bool × Ty)) :
    templateAdmissibleFields fs = fs.all (fun p => templateAdmissible p.2.2) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨name, optional, ty⟩ := p
    simp only [templateAdmissibleFields, List.all_cons, ih]

/-- The list equation used by `templateAdmissible_of_closed` for row admission. -/
theorem templateAdmissibleItems_eq_all (ts : List Ty) :
    templateAdmissibleItems ts = ts.all templateAdmissible := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [templateAdmissibleItems, List.all_cons, ih]

theorem templateAdmissible_of_closed (t : Ty) (h : closed t = true) :
    templateAdmissible t = true := by
  induction t with
  | record fs ih =>
    simp only [closed, closedFields_eq_all, List.all_eq_true] at h
    simp only [templateAdmissible, templateAdmissibleFields_eq_all, List.all_eq_true]
    exact fun p hp => ih p hp (h p hp)
  | tuple ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    simp only [templateAdmissible, templateAdmissibleItems_eq_all, List.all_eq_true]
    exact fun t ht => ih t ht (h t ht)
  | app name ts ih =>
    simp only [closed, templateAdmissible] at h ⊢
    exact h
  | _ => aesop (add norm simp [closed, templateAdmissible])

theorem varsOfFields_nil {fs : List (String × Bool × Ty)} (h : ∀ p ∈ fs, varsOf p.2.2 = []) :
    varsOfFields fs = [] := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [varsOfFields, h _ List.mem_cons_self, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

theorem varsOfItems_nil {ts : List Ty} (h : ∀ t ∈ ts, varsOf t = []) : varsOfItems ts = [] := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [varsOfItems, h _ List.mem_cons_self, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

theorem varsOf_eq_nil_of_closed (t : Ty) (h : closed t = true) : varsOf t = [] := by
  induction t with
  | record fs ih =>
    simp only [closed, closedFields_eq_all, List.all_eq_true] at h
    rw [varsOf]
    exact varsOfFields_nil fun p hp => ih p hp (h p hp)
  | tuple ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    rw [varsOf]
    exact varsOfItems_nil fun t ht => ih t ht (h t ht)
  | app n ts ih =>
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    rw [varsOf]
    exact varsOfItems_nil fun t ht => ih t ht (h t ht)
  | _ => aesop (add norm simp [closed, varsOf])

end Ty

/-- The operations whose own type arguments are closed: every one but a `Deferred.make` spelled
at a parameter. The checker's rows are closed in their type arguments, since a program's
annotations are closed types; a type argument with a parameter would make the answer bind a
parameter its request does not mention. -/
def NativeOp.typeArgsClosed : NativeOp → Bool
  | .deferredMakeOf value error => value.closed && error.closed
  | _ => true

/-- Every native row whose type arguments are closed has an admissible template: a parameter sits
only under a handle or a product, never under a union. -/
theorem NativeOp.row_templateAdmissible (op : NativeOp) (h : op.typeArgsClosed = true) :
    (NativeOp.row op).request.templateAdmissible = true ∧
      (NativeOp.row op).answer.templateAdmissible = true ∧
      (NativeOp.row op).error.templateAdmissible = true := by
  cases op with
  | scopeMake strategy => cases strategy <;> exact ⟨rfl, rfl, rfl⟩
  | deferredMakeOf value error =>
    have hc := Bool.and_eq_true_iff.mp h
    refine ⟨rfl, ?_, rfl⟩
    show (Ty.deferredOf value error).templateAdmissible = true
    simp only [Ty.templateAdmissible, Ty.templateAdmissible_of_closed _ hc.1,
      Ty.templateAdmissible_of_closed _ hc.2, Bool.and_self]
  | _ => exact ⟨rfl, rfl, rfl⟩

/-- Every native row whose type arguments are closed is well scoped: every parameter of its
answer and error is one its request mentions or, at a term row, one its term's result template
mentions (`Ref.modify`'s `B`, which `bindTerm` binds from the term's type). So the match binds
every parameter the row answers. -/
theorem NativeOp.row_wellScoped (op : NativeOp) (h : op.typeArgsClosed = true) :
    ((NativeOp.row op).answer.varsOf ++ (NativeOp.row op).error.varsOf).all (fun i =>
      (NativeOp.row op).request.varsOf.contains i ||
        op.binder?.any fun b => b.1.result.varsOf.contains i) = true := by
  cases op with
  | scopeMake strategy => cases strategy <;> rfl
  | deferredMakeOf value error =>
    have hc := Bool.and_eq_true_iff.mp h
    simp only [NativeOp.row, Ty.varsOf, Ty.varsOf_eq_nil_of_closed _ hc.1,
      Ty.varsOf_eq_nil_of_closed _ hc.2, List.append_nil, List.all_nil]
  | _ => rfl

/-- A native row whose operation carries no term is well scoped as a host row is
(`Row.wellScoped`): its request mentions every parameter it answers. -/
theorem NativeOp.row_wellScoped_of_none (op : NativeOp) (h : op.typeArgsClosed = true)
    (hb : op.binder? = none) : (NativeOp.row op).wellScoped = true := by
  have hs := NativeOp.row_wellScoped op h
  rw [hb] at hs
  simpa only [Row.wellScoped, Option.any_none, Bool.or_false] using hs

/-! ## The occurrences of a template's parameters (decisions row 42)

`paramOccurrences` lists each occurrence of a parameter in a template, in the order of the walk.
The argument of an invariant handle (`refOf`, `deferredOf`) is flagged. The laws of the match by
bounds read the list (`Bounds.mem_varsOf_args`). -/

namespace Ty

/-- The carrier of `paramOccurrences`: the node's own parameter when it is one, and its
occurrence list. -/
abbrev OccCarrier := Option Nat × List (Nat × Bool)

/-- A handle argument's occurrences: the argument itself, flagged as an anchor, when it is a
parameter, else its own occurrences. -/
def anchorOcc : OccCarrier → List (Nat × Bool)
  | (some i, _) => [(i, true)]
  | (none, occ) => occ

/-- The occurrence fold. A record's fields are read in canonical order.
A nominal argument is read at its declaration's variance, which may be
contravariant, so no occurrence under a reference is an anchor. -/
def paramOccurrencesAlg : TyAlgebra (fun _ => OccCarrier) where
  ty_never := (none, [])
  ty_unit := (none, [])
  ty_nat := (none, [])
  ty_int := (none, [])
  ty_string := (none, [])
  ty_bool := (none, [])
  ty_handle _ := (none, [])
  ty_option a := (none, a.2)
  ty_list a := (none, a.2)
  ty_prod a b := (none, a.2 ++ b.2)
  ty_except e a := (none, e.2 ++ a.2)
  ty_exitOf a e := (none, a.2 ++ e.2)
  ty_causeOf e := (none, e.2)
  ty_fiberOf a e := (none, a.2 ++ e.2)
  ty_union a b := (none, a.2 ++ b.2)
  ty_lit _ := (none, [])
  ty_refOf a := (none, anchorOcc a)
  ty_deferredOf a e := (none, anchorOcc a ++ anchorOcc e)
  ty_var i := (some i, [(i, false)])
  ty_unknown := (none, [])
  ty_record fs := (none, (canon fs).flatMap fun p => p.2.2.2)
  ty_map k v := (none, k.2 ++ v.2)
  ty_tuple ts := (none, ts.flatMap Prod.snd)
  ty_app _ ts := (none, ts.flatMap fun r => r.2.map fun o => (o.1, false))
  ty_null := (none, [])
  ty_undefined := (none, [])
  ty_number := (none, [])
  ty_bytes := (none, [])

/-- A template's parameter occurrences, each flagged when it is the direct
argument of an invariant handle. -/
def paramOccurrences (t : Ty) : List (Nat × Bool) := (cata_ty paramOccurrencesAlg t).2

/-! ### The proof's pieces -/

/-! Five facts of lists that the proofs below read are in `Effect4.Constructive.List`
(`src/Effect4/Data/Constructive.lean`): `flatMap_congr`, `mem_zip_map_self`, `mem_zip_middle`,
`eq_of_mem_zip_map` and `lookup_of_mem_nodup`. -/
open Effect4.Constructive.List (flatMap_congr mem_zip_map_self mem_zip_middle eq_of_mem_zip_map
  lookup_of_mem_nodup)

/-- A type is a parameter or is not one. -/
theorem var_or_ne (x : Ty) : (∃ i, x = .var i) ∨ ∀ i, x ≠ .var i := by
  cases x
  case var i => exact Or.inl ⟨i, rfl⟩
  all_goals exact Or.inr fun _ h => Ty.noConfusion h

/-! #### The occurrence list names the template's parameters, child by child -/

/-- The field companion of `varsOf` is a `flatMap`. -/
theorem varsOfFields_eq_flatMap (fs : List (String × Bool × Ty)) :
    varsOfFields fs = fs.flatMap fun p => varsOf p.2.2 := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [varsOfFields, ih, List.flatMap_cons]

/-- The item companion of `varsOf` is a `flatMap`. -/
theorem varsOfItems_eq_flatMap (ts : List Ty) : varsOfItems ts = ts.flatMap varsOf := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [varsOfItems, ih, List.flatMap_cons]


/-- An anchor flag changes no parameter of the list. -/
theorem anchorOcc_firsts (x : Ty) :
    (anchorOcc (cata_ty paramOccurrencesAlg x)).map Prod.fst =
      (paramOccurrences x).map Prod.fst := by
  cases x <;> rfl

/-- A record's occurrences, field by field in canonical order. -/
theorem paramOccurrences_record (fs : List (String × Bool × Ty)) :
    paramOccurrences (.record fs) = (canon fs).flatMap fun p => paramOccurrences p.2.2 := by
  rw [paramOccurrences, cata_ty_record]
  show ((canon (fs.map fun p => (p.1, prodMapSnd (cata_ty paramOccurrencesAlg) p.2))).flatMap
    fun p => p.2.2.2) = _
  rw [canon, Field.canonBy_map, List.flatMap_map]
  rfl

/-- A tuple's occurrences, item by item. -/
theorem paramOccurrences_tuple (ts : List Ty) :
    paramOccurrences (.tuple ts) = ts.flatMap paramOccurrences := by
  rw [paramOccurrences, cata_ty_tuple]
  show (ts.map (cata_ty paramOccurrencesAlg)).flatMap Prod.snd = _
  rw [List.flatMap_map]
  rfl

/-- A nominal reference's occurrences, argument by argument, with every flag down. -/
theorem paramOccurrences_app (n : String) (ts : List Ty) :
    paramOccurrences (.app n ts) =
      ts.flatMap fun x => (paramOccurrences x).map fun o => (o.1, false) := by
  rw [paramOccurrences, cata_ty_app]
  show (ts.map (cata_ty paramOccurrencesAlg)).flatMap
    (fun r => r.2.map fun o => (o.1, false)) = _
  rw [List.flatMap_map]
  rfl

/-- A union of members that each name their parameters names them too. -/
theorem paramOccurrences_firsts_ofMembers : ∀ xs : List Ty,
    (∀ x ∈ xs, (paramOccurrences x).map Prod.fst = varsOf x) →
      (paramOccurrences (ofMembers xs)).map Prod.fst = varsOf (ofMembers xs)
  | [], _ => rfl
  | [x], h => h x List.mem_cons_self
  | x :: y :: ys, h => by
    show (paramOccurrences x ++ paramOccurrences (ofMembers (y :: ys))).map Prod.fst =
      varsOf x ++ varsOf (ofMembers (y :: ys))
    rw [List.map_append, h x List.mem_cons_self,
      paramOccurrences_firsts_ofMembers (y :: ys) fun z hz => h z (List.mem_cons_of_mem _ hz)]

/-- **The occurrence list of a normal template names exactly its parameters**, in `varsOf`'s order. -/
theorem paramOccurrences_firsts {t : Ty} (ht : Normal t) :
    (paramOccurrences t).map Prod.fst = varsOf t := by
  induction ht with
  | option _ ih | list _ ih | causeOf _ ih => exact ih
  | refOf _ ih => exact (anchorOcc_firsts _).trans ih
  | prod _ _ _ _ iha ihb | except _ _ iha ihb | exitOf _ _ iha ihb | fiberOf _ _ iha ihb
  | map _ _ iha ihb =>
    exact (List.map_append ..).trans (congr (congrArg (· ++ ·) iha) ihb)
  | deferredOf _ _ iha ihb =>
    exact (List.map_append ..).trans (congr (congrArg (· ++ ·) ((anchorOcc_firsts _).trans iha))
      ((anchorOcc_firsts _).trans ihb))
  | row r _ _ _ ih =>
    obtain ⟨elems, _⟩ := r
    exact paramOccurrences_firsts_ofMembers elems ih
  | record _ hasc ih =>
    rename_i fs _
    rw [paramOccurrences_record, show canon fs = fs from Field.canonBy_of_ascending fs hasc, varsOf,
      varsOfFields_eq_flatMap, List.map_flatMap]
    exact flatMap_congr fun p hp => ih p hp
  | tuple _ _ ih =>
    rename_i ts _ _
    rw [paramOccurrences_tuple, varsOf, varsOfItems_eq_flatMap, List.map_flatMap]
    exact flatMap_congr fun x hx => ih x hx
  | app _ _ ih =>
    rename_i n ts _ _
    rw [paramOccurrences_app, varsOf, varsOfItems_eq_flatMap, List.map_flatMap]
    refine flatMap_congr fun x hx => ?_
    rw [List.map_map]
    exact ih x hx
  | _ => rfl

/-- The heads whose arguments `paramOccurrencesAlg` flags as anchors: the invariant handles. -/
def anchorsArgs : Ty → Bool
  | .refOf _ | .deferredOf _ _ => true
  | _ => false

/-- A child's block of its parent's occurrence list. Under an invariant handle a parameter child's
block is flagged as an anchor. -/
def childOcc (h : Bool) (x : Ty) : List (Nat × Bool) :=
  bif h then anchorOcc (cata_ty paramOccurrencesAlg x) else paramOccurrences x

/-- **A parent's occurrence list is its children's blocks, in argument order.** -/
theorem paramOccurrences_args {t : Ty} (hv : ∀ i, t ≠ .var i) (happ : ∀ n ts, t ≠ .app n ts) :
    paramOccurrences t = t.args.flatMap fun p => childOcc (anchorsArgs t) p.2 := by
  cases t
  case var i => exact absurd rfl (hv i)
  case app n ts => exact absurd rfl (happ n ts)
  case record fs =>
    rw [paramOccurrences_record]
    simp only [args, List.flatMap_map]
    rfl
  case tuple ts =>
    rw [paramOccurrences_tuple]
    simp only [args, List.flatMap_map]
    rfl
  all_goals
    simp only [args, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-! #### What an instance's normal form is made of -/

/-- A child list read off the parent's by one map pairs each child with its image. It is a step of
`template-match-complete`, and `instance_members` reads it. -/
theorem args_zip_of_map {τ : Subst} {t m : Ty}
    (h : m.args = t.args.map fun p => (p.1, (instantiate τ p.2).normalize)) :
    ∀ p ∈ t.args.zip m.args, p.1.1 = p.2.1 ∧ (p.2.2 = (instantiate τ p.1.2).normalize ∨
      (p.1.1 = .co ∧ p.2.2 ∈ (instantiate τ p.1.2).normalize.factors)) := by
  intro p hp
  rw [h] at hp
  have e := mem_zip_map_self hp
  exact ⟨(congrArg Prod.fst e).symm, Or.inl (congrArg Prod.snd e)⟩

/-- A field map that keeps every name and flag commutes with the canonical order. It is a step of
`template-match-complete`, and `instance_members` and `Bounds.instance_shape` read it. -/
theorem canon_map_payload (fs : List (String × Bool × Ty)) (f : Ty → Ty) :
    canon (fs.map fun q => (q.1, q.2.1, f q.2.2)) =
      (canon fs).map fun q => (q.1, q.2.1, f q.2.2) :=
  Field.canonBy_map (fun c : Bool × Ty => (c.1, f c.2)) fs

/-- **The members of a template's instance, read through the template's head.** Take a normal
template that is not a parameter, a union or a nominal reference. Every member of its instance's
normal form has the template's head. Each of the member's children is the corresponding child's
instance in normal form, or, under a product, one of that normal form's factors. The instance has a
member unless the template is `never`. It is a step of
`template-match-complete`, and `Bounds.below_args` reads it. -/
theorem instance_members (τ : Subst) {t : Ty} (ht : Normal t) (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) (happ : ∀ n ts, t ≠ .app n ts) :
    (t = .never ∨ ∃ m, m ∈ (instantiate τ t).normalize.members) ∧
    ∀ m ∈ (instantiate τ t).normalize.members, sameHead t m = true ∧
      ∀ p ∈ t.args.zip m.args, p.1.1 = p.2.1 ∧ (p.2.2 = (instantiate τ p.1.2).normalize ∨
        (p.1.1 = .co ∧ p.2.2 ∈ (instantiate τ p.1.2).normalize.factors)) := by
  induction ht with
  | never => exact ⟨Or.inl rfl, fun m hm => absurd hm List.not_mem_nil⟩
  | var i => exact absurd rfl (hv i)
  | prod _ _ _ _ _ _ =>
    rename_i a b _ _ _ _ _ _
    have hmem : ((instantiate τ (.prod a b)).normalize).members =
        (normalizeRow (productMembers (instantiate τ a).normalize
          (instantiate τ b).normalize)).elems :=
      OrderProof.members_normalize_prod _ _
    rw [hmem]
    refine ⟨Or.inr ?_, fun m hm => ?_⟩
    · obtain ⟨x, hx⟩ := OrderProof.normal_factors_nonempty _ (normal_normalize (instantiate τ a))
      obtain ⟨y, hy⟩ := OrderProof.normal_factors_nonempty _ (normal_normalize (instantiate τ b))
      have hxy : Ty.prod x y ∈ productMembers (instantiate τ a).normalize
          (instantiate τ b).normalize :=
        List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩
      obtain ⟨z, hz, -⟩ := normalizeRow_coverage _ (.prod x y) hxy
      exact ⟨z, hz⟩
    · have hm' := ((mem_normalizeRow m _).mp hm).1
      obtain ⟨x, hx, hm'⟩ := List.mem_flatMap.mp hm'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm'
      refine ⟨rfl, fun p hp => ?_⟩
      simp only [args, List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨rfl, Or.inr ⟨rfl, hx⟩⟩
      · exact ⟨rfl, Or.inr ⟨rfl, hy⟩⟩
  | row r _ _ _ ih =>
    obtain ⟨elems, _⟩ := r
    cases elems with
    | nil => exact ⟨Or.inl rfl, fun m hm => absurd hm List.not_mem_nil⟩
    | cons x xs =>
      cases xs with
      | nil => exact ih x List.mem_cons_self hv hu happ
      | cons y ys => exact absurd rfl (hu x (ofMembers (y :: ys)))
  | record _ hasc _ =>
    rename_i fs _ _
    have hc : canon fs = fs := Field.canonBy_of_ascending fs hasc
    have hJ : (instantiate τ (.record fs)).normalize =
        .record (fs.map fun q => (q.1, q.2.1, (instantiate τ q.2.2).normalize)) := by
      rw [instantiate, instantiateFields_eq_map, normalize_record, canon_map_payload, hc,
        List.map_map]
      rfl
    rw [hJ]
    refine ⟨Or.inr ⟨_, List.mem_singleton_self _⟩, fun m hm => ?_⟩
    rw [members, List.mem_singleton] at hm
    subst hm
    have hc' : canon (fs.map fun q => (q.1, q.2.1, (instantiate τ q.2.2).normalize)) =
        fs.map fun q => (q.1, q.2.1, (instantiate τ q.2.2).normalize) :=
      (canon_map_payload fs fun x => (instantiate τ x).normalize).trans (by rw [hc])
    refine ⟨?_, args_zip_of_map ?_⟩
    · simp only [sameHead, hc, hc', List.map_map, decide_eq_true_eq]
      rfl
    · simp only [args, hc, hc', List.map_map]
      rfl
  | tuple _ hlen _ =>
    rename_i ts _ _
    have hJ : (instantiate τ (.tuple ts)).normalize =
        .tuple (ts.map fun x => (instantiate τ x).normalize) := by
      rw [instantiate, instantiateItems_eq_map,
        normalize_tuple_of_ne _ (by rw [List.length_map]; exact hlen), normalizeItems_eq_map,
        List.map_map]
      rfl
    rw [hJ]
    refine ⟨Or.inr ⟨_, List.mem_singleton_self _⟩, fun m hm => ?_⟩
    rw [members, List.mem_singleton] at hm
    subst hm
    refine ⟨?_, args_zip_of_map ?_⟩
    · simp only [sameHead, List.length_map, decide_eq_true_eq]
    · simp only [args, List.map_map]
      rfl
  | app _ _ =>
    rename_i n ts _ _ _
    exact absurd rfl (happ n ts)
  | _ =>
    simp only [instantiate, normalize, members]
    refine ⟨Or.inr ⟨_, List.mem_singleton_self _⟩, fun m hm => ?_⟩
    rw [List.mem_singleton] at hm
    subst hm
    exact ⟨by simp only [sameHead, decide_eq_true_eq], args_zip_of_map rfl⟩

/-- **An instance's normal form reads only the normal forms of the template's own bindings.** It is a step of
`template-match-complete`, and `Bounds.covers` reads it. -/
theorem normalize_instantiate_congr {σ τ : Subst} (t : Ty)
    (h : ∀ i ∈ varsOf t, (instantiate σ (.var i)).normalize = (instantiate τ (.var i)).normalize) :
    (instantiate σ t).normalize = (instantiate τ t).normalize := by
  induction t with
  | var i => exact h i List.mem_cons_self
  | option x ih | list x ih | causeOf x ih | refOf x ih =>
    simp only [instantiate, normalize, ih h]
  | prod a b iha ihb | except a b iha ihb | exitOf a b iha ihb | fiberOf a b iha ihb
  | union a b iha ihb | deferredOf a b iha ihb | map a b iha ihb =>
    simp only [instantiate, normalize, iha fun i hi => h i (List.mem_append_left _ hi),
      ihb fun i hi => h i (List.mem_append_right _ hi)]
  | record fs ih =>
    have hf : ∀ q ∈ fs, (instantiate σ q.2.2).normalize = (instantiate τ q.2.2).normalize :=
      fun q hq => ih q hq fun i hi => h i (by
        rw [varsOf, varsOfFields_eq_flatMap]
        exact List.mem_flatMap.mpr ⟨q, hq, hi⟩)
    rw [instantiate, instantiate, normalize, normalize, instantiateFields_eq_map,
      instantiateFields_eq_map, normalizeFields_eq_map, normalizeFields_eq_map, List.map_map,
      List.map_map]
    exact congrArg (fun l => Ty.record (canon l)) (List.map_congr_left fun q hq => by
      simp only [Function.comp_def, normPayload, hf q hq])
  | tuple ts ih | app _ ts ih =>
    have hf : ∀ x ∈ ts, (instantiate σ x).normalize = (instantiate τ x).normalize :=
      fun x hx => ih x hx fun i hi => h i (by
        rw [varsOf, varsOfItems_eq_flatMap]
        exact List.mem_flatMap.mpr ⟨x, hx, hi⟩)
    rw [instantiate, instantiate, normalize, normalize, instantiateItems_eq_map,
      instantiateItems_eq_map, normalizeItems_eq_map, normalizeItems_eq_map, List.map_map,
      List.map_map]
    exact congrArg _ (List.map_congr_left fun x hx => by simp only [Function.comp_def, hf x hx])
  | _ => rfl

/-! #### The request: under the instance, and its head -/

/-- A normal union is a normal member beside a normal, non-empty rest. It is a step of
`template-match-complete`, and `Bounds.cands_below` and `Bounds.covers` read it. -/
theorem normal_union_inv {c d : Ty} (h : Normal (.union c d)) :
    Normal c ∧ Normal d ∧ isMember c = true ∧ d ≠ .never := by
  generalize hu : Ty.union c d = u at h
  cases h with
  | row r children atoms maximal =>
    obtain ⟨elems, hasc⟩ := r
    match elems, hasc, children, atoms, maximal, hu with
    | [], _, _, _, _, hu => exact nomatch hu
    | [x], _, _, atoms, _, hu =>
      have hx := atoms x List.mem_cons_self
      simp only [ofMembers] at hu
      rw [← hu] at hx
      exact Bool.noConfusion hx
    | x :: y :: ys, hasc, children, atoms, maximal, hu =>
      simp only [ofMembers, union.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      refine ⟨children _ List.mem_cons_self, ?_, atoms _ List.mem_cons_self, ?_⟩
      · exact Normal.row ⟨y :: ys, List.Pairwise.of_cons hasc⟩
          (fun t ht => children t (List.mem_cons_of_mem _ ht))
          (fun t ht => atoms t (List.mem_cons_of_mem _ ht))
          (fun a ha b hb => maximal a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      · cases ys with
        | nil =>
          intro hy
          have hm := atoms y (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [ofMembers] at hy
          rw [hy] at hm
          exact Bool.noConfusion hm
        | cons z zs => exact fun h => nomatch h
  | _ => exact nomatch hu

/-- A factor is below the type it factors. It is a step of
`template-match-complete`, and `Bounds.below_args` reads it. -/
theorem sub_of_mem_factors {x y : Ty} (hx : x ∈ y.factors) : sub x y = true := by
  unfold factors at hx
  split at hx
  · rw [List.mem_singleton] at hx
    subst hx
    exact sub_refl _
  · exact OrderProof.member_sub_self hx

/-- Every head but a nominal reference reads its arguments covariantly or invariantly. It is a step of
`template-match-complete`, and `Bounds.below_args`, `Bounds.cands_below` and `Bounds.covers` read it. -/
theorem args_co_or_inv {t : Ty} (happ : ∀ n ts, t ≠ .app n ts) :
    ∀ p ∈ t.args, p.1 = .co ∨ p.1 = .inv := by
  intro p hp
  cases t
  case app n ts => exact absurd rfl (happ n ts)
  case record fs =>
    simp only [args, List.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    exact Or.inl rfl
  case tuple ts =>
    simp only [args, List.mem_map] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact Or.inl rfl
  all_goals simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hp
  all_goals aesop

/-- Every child of an admissible template is admissible, and a union's children are closed. It is a step of
`template-match-complete`, and `Bounds.TemplateOK.args` reads it. -/
theorem templateAdmissible_args {t : Ty} (h : templateAdmissible t = true) :
    ∀ p ∈ t.args, templateAdmissible p.2 = true := by
  intro p hp
  cases t
  case union a b =>
    simp only [templateAdmissible, Bool.and_eq_true] at h
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact templateAdmissible_of_closed _ h.1
    · exact templateAdmissible_of_closed _ h.2
  case record fs =>
    rw [templateAdmissible, templateAdmissibleFields_eq_all, List.all_eq_true] at h
    simp only [args, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact h q (mem_canon hq)
  case tuple ts =>
    rw [templateAdmissible, templateAdmissibleItems_eq_all, List.all_eq_true] at h
    simp only [args, List.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact h x hx
  case app n ts =>
    rw [templateAdmissible, closedItems_eq_all, List.all_eq_true] at h
    simp only [args, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact templateAdmissible_of_closed _ (h q.1 (List.fst_mem_of_mem_zipIdx hq))
  all_goals simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hp
  all_goals aesop (add norm simp [templateAdmissible])

end Ty

/-- **The order is sound for membership.** Whatever the guard admits, the value really does
inhabit the template's instance: this is `hasTy_sub`, named here as the half of the guard's
worth that a consumer may rely on. -/
theorem sub_sound (a b : Ty) (v : Effect4.Machine.Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true :=
  hasTy_sub a b v allocated hsub hv

/-- **The order is NOT complete for membership**, and the witness is one line of TypeScript:
`Option<number | string>` and `Option<number> | Option<string>` have the same values, and
`sub` refuses the pair because it is structural — the left node is an `option` and the right
one is a row. Anything that reads `sub` as "the value sets are included" is wrong, and this
theorem is what makes that a fact of the tree rather than a caveat in a comment. -/
theorem sub_not_complete :
    (∀ v : Effect4.Machine.Val, Val.hasTy v (.option (.union .nat .string)) = true →
        Val.hasTy v (.union (.option .nat) (.option .string)) = true) ∧
      Ty.sub (.option (.union .nat .string)) (.union (.option .nat) (.option .string))
        = false := by
  refine ⟨fun v hv => ?_, ?_⟩
  · cases v
    case none => rfl
    case some x => exact hv
    all_goals exact Bool.noConfusion hv
  -- Plain `decide` gets stuck here: `Ty.sub` is a well-founded recursion, which the
  -- elaborator's reduction does not unfold. The kernel does reduce it, so `decide +kernel`
  -- closes this fact (TY-15, tested); the proof keeps the view's own lemmas so each step is
  -- one of the order's rules
  · have hsn : Ty.sub .string .nat = false :=
      Ty.sub_eq_false_of_not_sameHead .string .nat rfl rfl rfl rfl rfl
    have hns : Ty.sub .nat .string = false :=
      Ty.sub_eq_false_of_not_sameHead .nat .string rfl rfl rfl rfl rfl
    have hun : Ty.sub (.union .nat .string) .nat = false := by
      rw [Ty.sub_union_left _ _ _ (fun h => Ty.noConfusion h), hsn, Bool.and_false]
    have hus : Ty.sub (.union .nat .string) .string = false := by
      rw [Ty.sub_union_left _ _ _ (fun h => Ty.noConfusion h), hns, Bool.false_and]
    rw [Ty.sub_union_right _ _ _ rfl, Ty.sub_args_option, Ty.sub_args_option]
    simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true, hun, hus, Bool.or_false]

end Effect4.Program
