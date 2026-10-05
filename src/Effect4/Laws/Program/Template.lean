import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics
import Effect4.Program.Typing
import Effect4.Program.Native
import Effect4.Program.SigApp
import Aesop

/-!
# Laws.Program.Template — the row-template calculus (decisions row 42)

`Ty.instantiate`, `Ty.infer` and `Ty.matchTemplate` (`Program/Ty.lean`) with their laws. A
match is sound by its own guard (`matchTemplate_sound`), whichever rule `join` picks, at the
normalized instance, and a list match puts every argument at its parameter's instance under the
bindings of the LAST step, because inference only widens (`matchTemplateArgs_widens`) and
instantiation carries a widening to every template (`cata_admits_instantiate`). On a closed
template the calculus is the identity and subsumption (`instantiate_closed`, `infer_closed`,
`matchTemplate_closed`), so a closed row types exactly as it did before the templates
(`rowTy_closed`, `rowTy_closed_some`). `closed` survives `normalize` (`closed_normalize`). The
`Ref` and `Deferred` rows are templates over their type parameters (the state plan's T3a), so the
native rows' profile holds at every operation whose own type arguments are closed
(`NativeOp.row_templateAdmissible`, `NativeOp.row_wellScoped`). The match's completeness on
anchored templates is a planned goal (`Ty.matchTemplate_complete_anchored`).
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

/-- The field a closed record's lookup finds is closed: the step of `infer_closed` at a
record field, which `inferFields` reads by name. -/
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

theorem infer_closed {join : Bool} (σ : Subst) (t r : Ty) (h : closed t = true) :
    infer σ t r join = σ := by
  revert h
  induction σ, t, r using infer.induct_unfolding join
      (motive_2 := fun σ ts _ result => closedItems ts = true → result = σ)
      (motive_3 := fun σ fs _ result => closedFields fs = true → result = σ)
  case case1 => intro h; cases h
  case case2 => intro h; cases h
  case case3 => intro h; cases h
  case case4 ih => exact ih
  case case5 ih => exact ih
  case case6 ih => exact ih
  case case7 ih => exact ih
  case case8 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case9 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case10 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case11 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case12 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case13 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case14 ih₁ ih₂ =>
    intro h
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case15 ih => exact ih
  case case16 ih => exact ih
  case case17 ih => exact ih
  case case18 => intro _; rfl
  -- a request union, member by member (`E4-CHECK-CE-018`): the template stays closed
  case case19 ih₁ ih₂ =>
    intro h
    exact (ih₂ h).trans (ih₁ h)
  case case20 => intro _; rfl
  case case21 => rfl
  case case22 ih h => exact ih h
  case case23 hl ih₁ ih₂ h => exact (ih₂ h).trans (ih₁ (closed_of_lookup hl h))
  case case24 ih₁ ih₂ h =>
    have hc := Bool.and_eq_true_iff.mp h
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  case case25 => rfl

/-- A match is sound: the request is below the template's instance at the bindings in the
checker's order, both sides normalized. -/
theorem matchTemplate_sound {join : Bool} (σ : Subst) (t r : Ty) (σ' : Subst)
    (h : matchTemplate σ t r join = some σ') :
    sub r.normalize (instantiate σ' t).normalize = true := by
  unfold matchTemplate at h
  aesop

/-- On a closed template the match is subsumption of the normal forms, and the seed. -/
theorem matchTemplate_closed {join : Bool} (σ : Subst) (t r : Ty) (h : closed t = true) :
    matchTemplate σ t r join = if sub r.normalize t.normalize then some σ else none := by
  simp only [matchTemplate, infer_closed σ t r h, instantiate_closed σ t h]

/-! ### What a list match binds, at the end of the list

`matchTemplateArgs` reads each argument's guard at the bindings of that argument's own step,
and an atom's answer is instantiated at the bindings of the last step. Between the two sits
one fact: inference only widens. A parameter it binds was `never` before, which admits
nothing, and a parameter it rebinds moves up the order (`infer`'s `join`). Instantiation
carries a widening to every template, as a condition on the admission algebra — every child
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

/-- Inference only widens: a new binding was `never`, a joined one moves up the order. -/
theorem infer_widens (σ : Subst) (t r : Ty) (join : Bool) : Widens σ (infer σ t r join) :=
  Widens.of_lookup (infer_widensSub σ t r join)

/-- A match widens its seed. -/
theorem matchTemplate_widens {join : Bool} {σ σ' : Subst} {t r : Ty}
    (h : matchTemplate σ t r join = some σ') : Widens σ σ' := by
  dsimp only [matchTemplate] at h
  split at h
  · cases h
    exact infer_widens σ t r join
  · exact nomatch h

/-- A list match widens its seed, step by step. -/
theorem matchTemplateArgs_widens {join : Bool} {σ σ' : Subst} {ps rs : List Ty}
    (h : matchTemplateArgs σ ps rs join = some σ') : Widens σ σ' := by
  induction ps generalizing rs σ with
  | nil =>
    cases rs with
    | nil => cases h; exact Widens.refl _
    | cons _ _ => exact nomatch h
  | cons p ps ih =>
    cases rs with
    | nil => exact nomatch h
    | cons r rs =>
      simp only [matchTemplateArgs, Option.bind_eq_some_iff] at h
      obtain ⟨σ₁, h₁, hrest⟩ := h
      exact (matchTemplate_widens h₁).trans (ih hrest)

end Ty

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
    simp only [rowTy, checkRow, Ty.matchTemplate_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, Bool.false_eq_true, ↓reduceIte, Except.toOption]
  | true =>
    simp only [rowTy, checkRow, Ty.matchTemplate_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, ↓reduceIte, hformed, Except.toOption,
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
    simp only [checkRow, Ty.matchTemplate_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  | true =>
    simp only [checkRow, Ty.matchTemplate_closed [] _ _ (Ty.closed_normalize _ hreq),
      Ty.normalize_idem, hsub, ↓reduceIte] at h
    split at h
    · cases h
    · simp only [Ty.instantiate_closed _ _ hans, Ty.instantiate_closed _ _ herr,
        Except.ok.injEq] at h
      exact ⟨rfl, h.symm⟩

/-- `instantiated-formation`: a successful row use retains the actual bindings and
strict formation of every substituted column. Typing consumes this through `rowTy`.
This is a static property; it makes no host reply or execution claim. -/
theorem rowTy_instantiated_formed {row : Row} {request : Ty} {ty : EffTy}
    (accepted : rowTy row request = some ty) :
    ∃ bindings, Ty.matchTemplate [] row.request.normalize request.normalize = some bindings ∧
      Formation.Formed (Formation.instantiatedSites row bindings) := by
  rw [rowTy_eq_some_iff] at accepted
  unfold checkRow at accepted
  split at accepted
  · cases accepted
  · rename_i bindings matched
    split at accepted
    · cases accepted
    · rename_i formed
      exact ⟨bindings, matched, (Formation.check_eq_none_iff _).mp formed⟩

/-- The precise diagnostic part of `instantiated-formation`: this refusal names
an actual failed column check after a successful template match. -/
theorem checkRow_formation_iff (row : Row) (request : Ty) (why : FormationRefusal) :
    checkRow row request = .error (.formation why) ↔
      ∃ bindings, Ty.matchTemplate [] row.request.normalize request.normalize = some bindings ∧
        Formation.check (Formation.instantiatedSites row bindings) = some why := by
  constructor
  · intro refused
    unfold checkRow at refused
    split at refused
    · cases refused
    · rename_i bindings matched
      split at refused
      · rename_i actual failed
        have same : actual = why := RowTypingRefusal.formation.inj (Except.error.inj refused)
        subst same
        exact ⟨bindings, matched, failed⟩
      · cases refused
  · rintro ⟨bindings, matched, failed⟩
    simp only [checkRow, matched, failed]

/-- Request mismatch retains its exact meaning and precedence. The formation
branch cannot be reported as a subtype mismatch by the shared row checker. -/
theorem checkRow_request_iff (row : Row) (request : Ty) :
    checkRow row request = .error .requestNotSubtype ↔
      Ty.matchTemplate [] row.request.normalize request.normalize = none := by
  cases matched : Ty.matchTemplate [] row.request.normalize request.normalize with
  | none => simp only [checkRow, matched]
  | some bindings =>
    simp only [checkRow, matched, reduceCtorEq]
    split <;> simp only [Except.error.injEq, reduceCtorEq]

/-! ## What a row's template may say, and what the guard buys (plan 1.8)

Three properties of the calculus, stated as theorems rather than left in prose.

`templateAdmissible` and `Row.wellScoped` are the two shapes a row's template must have for
inference to mean anything, and both hold of every native row of this cut. `sub_sound` and
`sub_not_complete` are the two halves of what the guard is worth: the order NEVER admits a
value the target would refuse, and it DOES refuse pairs whose value sets agree. A checker
built on it can lose a program, never mistype one — L4's anchored completeness is the
statement that says which programs it loses, and it is not this one.

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
    simp only [closed, closedItems_eq_all, List.all_eq_true] at h
    simp only [templateAdmissible, templateAdmissibleItems_eq_all, List.all_eq_true]
    exact fun t ht => ih t ht (h t ht)
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
answer and error is one its request mentions, so inference binds it from the request. -/
theorem NativeOp.row_wellScoped (op : NativeOp) (h : op.typeArgsClosed = true) :
    (NativeOp.row op).wellScoped = true := by
  cases op with
  | scopeMake strategy => cases strategy <;> rfl
  | deferredMakeOf value error =>
    have hc := Bool.and_eq_true_iff.mp h
    simp only [Row.wellScoped, NativeOp.row, Ty.varsOf, Ty.varsOf_eq_nil_of_closed _ hc.1,
      Ty.varsOf_eq_nil_of_closed _ hc.2, List.append_nil, List.all_nil]
  | _ => rfl

/-! ## The match's completeness on anchored templates (planned goal)

`matchTemplate_sound` is the guard's half. The other half says which requests the match finds a
substitution for. A parameter whose first occurrence in `infer`'s walk is an invariant handle's
argument (`refOf`, `deferredOf`) is bound there to a type equivalent to every substitution's, so
the later occurrences need no rebinding. The walk reaches that argument in every union member
unless a member holds `never` on the way, which the order admits below any handle; then a
covariant occurrence binds first (`docs/research/2026-10-04-seat-T3a/AnchoredGoal.lean`). -/

namespace Ty

/-- The carrier of `paramOccurrences`: the node's own parameter when it is one, and its
occurrence list. -/
abbrev OccCarrier := Option Nat × List (Nat × Bool)

/-- A handle argument's occurrences: the argument itself, flagged as an anchor, when it is a
parameter, else its own occurrences. -/
def anchorOcc : OccCarrier → List (Nat × Bool)
  | (some i, _) => [(i, true)]
  | (none, occ) => occ

/-- The occurrence fold. A record's fields are read in canonical order, as `infer` reads a
normal request's. A nominal argument is read at its declaration's variance, which may be
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

/-- A template's parameter occurrences in `infer`'s order, each flagged when it is the direct
argument of an invariant handle. -/
def paramOccurrences (t : Ty) : List (Nat × Bool) := (cata_ty paramOccurrencesAlg t).2

/-- Each parameter's first occurrence in the list is flagged, `seen` the parameters already met. -/
def anchoredFrom (seen : List Nat) : List (Nat × Bool) → Bool
  | [] => true
  | (i, anchor) :: rest => (anchor || seen.contains i) && anchoredFrom (i :: seen) rest

/-- Every parameter of the template first occurs as an invariant handle's argument. -/
def anchored (t : Ty) : Bool := anchoredFrom [] t.paramOccurrences

/-- No `never` outside an invariant handle's argument, where a member of a request union could
stand below a handle the template walks to. -/
def bottomFreeAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := true
  ty_string := true
  ty_bool := true
  ty_handle _ := true
  ty_option a := a
  ty_list a := a
  ty_prod a b := a && b
  ty_except e a := e && a
  ty_exitOf a e := a && e
  ty_causeOf e := e
  ty_fiberOf a e := a && e
  ty_union a b := a && b
  ty_lit _ := true
  ty_refOf _ := true
  ty_deferredOf _ _ := true
  ty_var _ := true
  ty_unknown := true
  ty_record fs := fs.all fun p => p.2.2
  ty_map k v := k && v
  ty_tuple ts := ts.all id
  ty_app _ ts := ts.all id
  ty_null := true
  ty_undefined := true
  ty_number := true
  ty_bytes := true

/-- A request type with no `never` outside an invariant handle's argument. -/
def bottomFree (t : Ty) : Bool := cata_ty bottomFreeAlg t

#guard anchored (.refOf (.var 0))
#guard anchored (.prod (.refOf (.var 0)) (.var 0))
#guard anchored (.prod (.deferredOf (.var 0) (.var 1)) (.var 1))
-- `Ref.make`'s bare parameter is not anchored: the match binds it at its first arm
#guard !anchored (.var 0)
#guard !anchored (.prod (.var 0) (.refOf (.var 0)))
#guard !bottomFree (.union (.prod .never (.lit "a")) (.prod (.refOf .string) (.lit "b")))
#guard bottomFree (.prod (.deferredOf .nat .never) .nat)

/-- **The match is complete on anchored templates** (planned goal; the claim
`template-match-anchored`, R4): at a normal, admissible template whose every parameter first
occurs as an invariant handle's argument, every normal request with no `never` outside such an
argument that some substitution puts under the instance has a match. Its soundness half is
`matchTemplate_sound`. The `bottomFree` premise is needed, not a convenience: a union member whose
anchor holds `never` binds the parameter at a covariant occurrence first, and the statement
without it is false for the repaired `infer` (tested,
`docs/research/2026-10-04-seat-T3a/AnchoredGoal.lean`). It does not establish completeness where
a parameter first occurs covariantly, under a union template, or under a nominal reference. -/
@[semantics "subtyping-algebra" (requirement := R4)]
proof_goal matchTemplate_complete_anchored {t r : Ty} {τ : Subst} (ht : Normal t)
    (hadm : t.templateAdmissible = true) (hanch : t.anchored = true) (hr : Normal r)
    (hbot : r.bottomFree = true) (hτ : sub r.normalize (t.instantiate τ).normalize = true) :
    ∃ σ, matchTemplate [] t r = some σ

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
