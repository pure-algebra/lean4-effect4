import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.References
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.UnionRule
import Effect4.Laws.Program.Eliminators
import Effect4.Program.Admission
import Effect4.Program.Bounds
import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Program.Definitions

/-!
# Laws.Program.Typing.Closed — the checker gives a formed program closed types

A type variable is formed in a template only (`Formation.HeadFormed`, decisions row 288, point
6 a). This module states what that clause buys: a program whose annotations are formed has closed
types, at every typing signature whose atoms and service carriers are closed (`check_closed`
and `typeOfProgram_closed`, the claim `checked-types-closed`).

The sections, in the order a proof reads them:

1. **Strict formation gives a closed type** (`Formation.closed_of_formed`). The judgment of a
   type's sites is the head judgment at each raw occurrence (`Formation.formed_sites_iff`), and
   outside a template no occurrence is a variable.
2. **Each type operation keeps closed types closed**: one lemma per operation the checker
   applies. `Ty.closed_normalize` and its steps are `Laws/Program/Template.lean`'s. A lifted
   rule keeps closed types closed when its member rule does (`UnionRule.lift_closed`,
   `Laws/Program/UnionRule.lean`), and the two record rules are its instances. An atom's scheme
   answers a closed type at closed arguments (`NativeAtom.Scheme.closed_apply`).
3. **The annotations of a program, as a fold** (`Formation.AnnotationsAll`). The collector
   `Formation.programAnnotations` is a path fold into lists. Through a homomorphism that reads
   no path, a path fold is the fold with no path (`foldMapAt_eff_fuse` and its siblings,
   `Laws/Program/PathFold.lean`). So "every annotation's type satisfies `P`" is a conjunction
   that follows the program's shape (`Formation.programAnnotations_all`). A program's expansion
   states what the program states (`Formation.annotationsAll_expandRefs`).
4. **Terms and causes** (`termTy_closed`, `causeTy_closed`).
5. **The six judgments** (`hasTy_closed` and its five siblings), one line per rule.
6. **The checker** (`check_closed`), **the whole-program checker** (`typeOfProgram_closed`), and
   the native signature (`closedSig_native`).
7. **An application's signature.** A declared service carrier is a strict formation site
   (`Formation.serviceSites`), so a formed input gives closed carriers (`closedSig_app`), and
   an admitted program has closed types with no premise (`AdmittedProgram.closed`).

Placement. Concept `subtyping-algebra`, requirements R1, R3 and R14. Reach: a closed
environment, a typing signature with closed atoms and closed service carriers (`ClosedSig`), and
a program whose annotations are formed outside a template. No premise is asked of a row: the row
rule checks strict formation of each instantiated column (`checkRow`), so its answer is closed
by section 1. No premise is asked of a layer reference. It does not establish a closed type of a
sketch with a gap, and nothing of a run. Its consumers are the premise of `ofSchema_schema`
(`Schema/Bridge.lean`), the type printer `ofTy` and the codec, and stage 6 of the study of a gap
with holes (`docs/research/2026-10-06-seat-GAP-study.md`): after it a gap is the only open leaf
of a sketch's type.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

/-! ## 1. Strict formation gives a closed type -/

namespace Formation

/-- **The judgment of a type's sites is the head judgment at each raw occurrence**, at the
sites' template flag. A step of `closed_of_formed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem formed_sites_iff {template : Bool} {path : List String} {ty : Ty} :
    Formed (sites template path ty) ↔ ∀ t ∈ nodes ty, HeadFormed template t := by
  constructor
  · intro h t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
    have hmem : ((nodes ty)[k], k) ∈ (nodes ty).zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hk)
    exact h _ (List.mem_map_of_mem hmem)
  · intro h site hsite
    obtain ⟨⟨t, k⟩, hmem, rfl⟩ := List.mem_map.mp hsite
    exact h t (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hmem))

/-- A field's raw occurrences are occurrences of its field list. A step of `closed_of_nodes`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mem_nodes_field {n : String} {o : Bool} {u t : Ty} :
    ∀ {fs : List (String × Bool × Ty)}, (n, o, u) ∈ fs → t ∈ nodes u →
      t ∈ foldMap_pos_list_prod_string_prod_bool_ty [] (· ++ ·) fs (fun t => [t])
  | [], hp, _ => absurd hp List.not_mem_nil
  | _ :: fs, hp, ht => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_append_left _ ht
    · exact List.mem_append_right _ (mem_nodes_field hp ht)

/-- An item's raw occurrences are occurrences of its item list. A step of `closed_of_nodes`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mem_nodes_item {u t : Ty} :
    ∀ {ts : List Ty}, u ∈ ts → t ∈ nodes u →
      t ∈ foldMap_pos_list_ty [] (· ++ ·) ts (fun t => [t])
  | [], hu, _ => absurd hu List.not_mem_nil
  | _ :: ts, hu, ht => by
    rcases List.mem_cons.mp hu with rfl | hu
    · exact List.mem_append_left _ ht
    · exact List.mem_append_right _ (mem_nodes_item hu ht)

/-- A type with no variable among its raw occurrences is closed. A step of `closed_of_formed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_of_nodes {ty : Ty} (h : ∀ t ∈ nodes ty, ∀ i, t ≠ .var i) :
    ty.closed = true := by
  induction ty with
  | var i => exact absurd rfl (h (.var i) (List.mem_singleton_self _) i)
  | option a ih | list a ih | causeOf a ih | refOf a ih =>
    exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)
  | prod a b iha ihb | except a b iha ihb | exitOf a b iha ihb | fiberOf a b iha ihb
  | union a b iha ihb | deferredOf a b iha ihb | map a b iha ihb =>
    exact Bool.and_eq_true_iff.mpr
      ⟨iha fun t ht => h t (List.mem_cons_of_mem _ (List.mem_append_left (nodes b) ht)),
        ihb fun t ht => h t (List.mem_cons_of_mem _ (List.mem_append_right (nodes a) ht))⟩
  | record fs ih =>
    rw [Ty.closed, Ty.closedFields_eq_all, List.all_eq_true]
    exact fun p hp => ih p hp fun t ht => h t (List.mem_cons_of_mem _ (mem_nodes_field hp ht))
  | tuple ts ih =>
    rw [Ty.closed, Ty.closedItems_eq_all, List.all_eq_true]
    exact fun u hu => ih u hu fun t ht => h t (List.mem_cons_of_mem _ (mem_nodes_item hu ht))
  | app n ts ih =>
    rw [Ty.closed, Ty.closedItems_eq_all, List.all_eq_true]
    exact fun u hu => ih u hu fun t ht => h t (List.mem_cons_of_mem _ (mem_nodes_item hu ht))
  | _ => rfl

/-- **Strict formation gives a closed type.** Outside a template the head judgment refuses a
variable, so a type whose sites are formed there holds none. The row rule and the record rule
of the checker check exactly this judgment, so each answers a closed type with no premise
(`closed_rowTy`, `argTy_closed`). A step of `check_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_of_formed {path : List String} {ty : Ty}
    (h : Formed (sites false path ty)) : ty.closed = true :=
  closed_of_nodes fun t ht i hvar => by
    have hf : HeadFormed false t := formed_sites_iff.mp h t ht
    rw [hvar] at hf
    exact Bool.noConfusion hf

/-- Every annotation of a program whose annotations are formed has a closed type. A step of
`check_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem annotations_closed {Op : Type} [ScopedOp Op] {e : Eff Op}
    (h : Formed (programSites e)) : ∀ x ∈ programAnnotations e, x.2.closed = true := by
  intro x hx
  obtain ⟨path, ty⟩ := x
  exact closed_of_formed (path := path) fun site hsite =>
    h site (List.mem_flatMap.mpr ⟨(path, ty), hx, hsite⟩)

end Formation

/-! ## 2. Each type operation keeps closed types closed -/

namespace Ty

/-- The tag residual of a closed type is closed: it keeps members. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_diffTag (tag : String) {t : Ty} (h : t.closed = true) :
    (diffTag tag t).closed = true :=
  closed_ofMembers _ fun x hx => closed_members t h x (List.mem_filter.mp hx).1

/-- A tagged member's payload is closed when the member is. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_payloadOf {tag : String} {m p : Ty} (hm : m.closed = true)
    (h : payloadOf tag m = some p) : p.closed = true := by
  unfold payloadOf at h
  split at h
  · split at h
    · cases h
      exact (Bool.and_eq_true_iff.mp hm).2
    · exact nomatch h
  · exact nomatch h

/-- The payload type of a tag in a closed type is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_payloadTy {tag : String} {t p : Ty} (ht : t.closed = true)
    (h : payloadTy tag t = some p) : p.closed = true := by
  have hall : ∀ x ∈ t.members.filterMap (payloadOf tag), x.closed = true := fun x hx => by
    obtain ⟨m, hm, hpay⟩ := List.mem_filterMap.mp hx
    exact closed_payloadOf (closed_members t ht m hm) hpay
  unfold payloadTy at h
  generalize t.members.filterMap (payloadOf tag) = ps at h hall
  cases ps with
  | nil => exact nomatch h
  | cons a as =>
    cases h
    exact closed_normalize _ (closed_ofMembers _ hall)

/-- A binding that `lookup` finds is one of the bindings. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem mem_of_lookup : ∀ {σ : Subst} {i : Nat} {t : Ty}, σ.lookup i = some t → (i, t) ∈ σ
  | [], _, _, h => nomatch h
  | (j, u) :: σ, i, t, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      rw [eq_of_beq heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- Bindings whose every type is closed: what a match reads from a closed request. -/
def ClosedSubst (σ : Subst) : Prop := ∀ b ∈ σ, b.2.closed = true

/-- **An instance at closed bindings is closed**, whatever the template: a bound parameter
becomes its binding, and a parameter that no binding names becomes `never`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_instantiate {σ : Subst} (hσ : ClosedSubst σ) (t : Ty) :
    (instantiate σ t).closed = true := by
  induction t with
  | var i =>
    rw [instantiate]
    cases hl : σ.lookup i with
    | none => rfl
    | some u => exact hσ (i, u) (mem_of_lookup hl)
  | record fs ih =>
    rw [instantiate, instantiateFields_eq_map, closed, closedFields_eq_all, List.all_eq_true]
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq
  | tuple ts ih =>
    rw [instantiate, instantiateItems_eq_map, closed, closedItems_eq_all, List.all_eq_true]
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact ih v hv
  | app n ts ih =>
    rw [instantiate, instantiateItems_eq_map, closed, closedItems_eq_all, List.all_eq_true]
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact ih v hv
  | _ => aesop (add norm simp [closed, instantiate])

end Ty

namespace Record

/-- A record member's field read answers a closed type. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_fieldOf {optional : Bool} {name : String} {m r : Ty} (hm : m.closed = true)
    (h : fieldOf optional name m = some r) : r.closed = true := by
  cases m with
  | record fields =>
    simp only [fieldOf, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨mayBeAbsent, type⟩, hfirst, h⟩ := h
    have htype : type.closed = true := by
      rw [Ty.closed, Ty.closedFields_eq_all, List.all_eq_true] at hm
      exact hm (name, mayBeAbsent, type) (Field.firstOf_mem hfirst)
    split at h
    · cases h
      exact htype
    · split at h
      · exact nomatch h
      · cases h
        exact htype
  | _ => exact nomatch h

/-- A record member's overwrite answers a closed type, at a closed replacement. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_setOf {name : String} {valueType m r : Ty} (hv : valueType.closed = true)
    (hm : m.closed = true) (h : setOf name valueType m = some r) : r.closed = true := by
  cases m with
  | record fields =>
    cases h
    rw [Ty.closed, Ty.closedFields_eq_all, List.all_eq_true] at hm
    refine Ty.closed_normalize _ ?_
    rw [Ty.closed, Ty.closedFields_eq_all, List.all_eq_true]
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hv
    · exact hm p (List.mem_filter.mp hp).1
  | _ => exact nomatch h

/-- The field read keeps closed types closed. It is a lifted rule (`UnionRule.lift`), and its
member rule `fieldOf` keeps closed types closed (`UnionRule.lift_closed`,
`Laws/Program/UnionRule.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_fieldType {optional : Bool} {target ty : Ty} {name : String}
    (ht : target.closed = true) (h : fieldType optional target name = some ty) :
    ty.closed = true :=
  UnionRule.lift_closed (fun _ _ hm hr => closed_fieldOf hm hr) h ht

/-- The field write keeps closed types closed, at a closed replacement: `UnionRule.lift_closed`
at the member rule `setOf`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_setType {target valueType ty : Ty} {name : String} (ht : target.closed = true)
    (hv : valueType.closed = true) (h : setType target name valueType = some ty) :
    ty.closed = true :=
  UnionRule.lift_closed (fun _ _ hm hr => closed_setOf hv hm hr) h ht

/-- A record term's type is the normal form of its declaration. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_check {fields : Fields} {names : List String} {types : List Ty} {ty : Ty}
    (hf : (Ty.record fields).closed = true) (h : check fields names types = some ty) :
    ty.closed = true := by
  simp only [check, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · cases h
    exact Ty.closed_normalize _ hf
  · exact nomatch h

/-- The two arms of a record tag decision keep members of the target's normal form. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_tagArms {tag : String} {t : Ty} {arms : Ty × Ty} (ht : t.closed = true)
    (h : tagArms tag t = some arms) : arms.1.closed = true ∧ arms.2.closed = true := by
  have hm := Ty.closed_members _ (Ty.closed_normalize t ht)
  simp only [tagArms] at h
  split at h
  · cases h
    exact ⟨Ty.closed_ofMembers _ fun x hx => hm x (List.mem_filter.mp hx).1,
      Ty.closed_ofMembers _ fun x hx => hm x (List.mem_filter.mp hx).1⟩
  · exact nomatch h

end Record

/-- A positional projection of a closed type is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Tuple.closed_project {index : Nat} {t : Ty} : ∀ {r : Ty}, t.closed = true →
    Tuple.project index t = some r → r.closed = true := by
  induction t with
  | tuple items _ =>
    intro r ht h
    rw [Ty.closed, Ty.closedItems_eq_all, List.all_eq_true] at ht
    exact ht r (List.mem_of_getElem? h)
  | prod first second _ _ =>
    intro r ht h
    have hc := Bool.and_eq_true_iff.mp ht
    have hmem : r ∈ [first, second] := List.mem_of_getElem? h
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hc.1
    · rw [List.mem_singleton.mp hmem]
      exact hc.2
  | union left right ihl ihr =>
    intro r ht h
    have hc := Bool.and_eq_true_iff.mp ht
    simp only [Tuple.project, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact UnionRule.closed_join (ihl hc.1 ha) (ihr hc.2 hb)
  | never =>
    intro r _ h
    cases h
    rfl
  | _ => exact fun _ h => nomatch h

/-- The tuple read keeps closed types closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Tuple.closed_typeAt {target ty : Ty} {index : Nat} (ht : target.closed = true)
    (h : Tuple.typeAt target index = some ty) : ty.closed = true :=
  Tuple.closed_project (Ty.closed_normalize target ht) h

/-- The element type that the option rule answers is closed when the target is: the guarded rule
answers the lifted rule's answer (`UnionRule.liftOne_some`, `UnionRule.lift_closed`). A step of
`Decision.closed_arms`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_optionTy {t item : Ty} (ht : t.closed = true)
    (h : optionTy t = some item) : item.closed = true :=
  UnionRule.lift_closed (fun _ _ closed answered => Member.option_closed closed answered)
    (UnionRule.liftOne_some h) ht

/-- What a decision's arms bind is closed, at a closed scrutinee. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Decision.closed_arms {d : Decision} {t : Ty} {e0 e1 : List Ty} (ht : t.closed = true)
    (h : d.arms t = some (e0, e1)) :
    (∀ x ∈ e0, x.closed = true) ∧ ∀ x ∈ e1, x.closed = true := by
  have hn := Ty.closed_normalize t ht
  cases d with
  | bool =>
    simp only [Decision.arms] at h
    split at h
    · cases h
      exact ⟨fun _ hx => (nomatch hx), fun _ hx => (nomatch hx)⟩
    · exact nomatch h
  | option =>
    simp only [Decision.arms] at h
    obtain ⟨a, hopt, heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    have ha := closed_optionTy ht hopt
    exact ⟨fun _ hx => (nomatch hx), fun x hx => by rw [List.mem_singleton.mp hx]; exact ha⟩
  | tag name =>
    simp only [Decision.arms] at h
    split at h
    · obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      exact ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact Ty.closed_payloadTy hn hp,
        fun x hx => by rw [List.mem_singleton.mp hx]; exact Ty.closed_diffTag name hn⟩
    · exact nomatch h
  | recordTag name =>
    obtain ⟨parts, hparts, heq⟩ := Option.map_eq_some_iff.mp h
    cases heq
    have hc := Record.closed_tagArms ht hparts
    exact ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hc.1,
      fun x hx => by rw [List.mem_singleton.mp hx]; exact hc.2⟩

/-- A fiber handle's two columns are closed when the handle's type is. The fiber rule is the
extended rule of its member rule (`UnionRule.extend`, `src/Effect4/Program/UnionRule.lean`), so
the fact is `UnionRule.extend_closed_pair` at the member fact `Member.fiber_closed`
(`src/Effect4/Laws/Program/Eliminators.lean`): the member rule's own answer is closed at a closed
fiber type, and `UnionRule.lift_closed_pair` covers the guarded rule's answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_fiberTy {t value error : Ty} (ht : t.closed = true)
    (h : fiberTy t = some (value, error)) : value.closed = true ∧ error.closed = true :=
  UnionRule.extend_closed_pair Member.fiber_closed h ht

/-- The element type of `Checker.listOf?` is closed when the target is. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_listOf {t item : Ty} (ht : t.closed = true)
    (h : Checker.listOf? t = some item) : item.closed = true :=
  UnionRule.extend_closed Member.list_closed h ht

/-- The value and error types of `Checker.exitOf?` are closed when the target is. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_exitOf {t : Ty} {pair : Ty × Ty} (ht : t.closed = true)
    (h : Checker.exitOf? t = some pair) : pair.1.closed = true ∧ pair.2.closed = true :=
  UnionRule.extend_closed_pair Member.exit_closed h ht


/-- The error column of `catchIf` is closed when the body's and the handler's are. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_catchIfError (test : Term) (caught : Nat) {b h : Ty} (hb : b.closed = true)
    (hh : h.closed = true) : (catchIfError test caught b h).closed = true := by
  unfold catchIfError
  split
  · exact hh
  · split
    · split
      · exact hh
      · exact UnionRule.closed_join hb hh
    · exact UnionRule.closed_join hb hh

/-! ### Templates and atoms

An atom's answer is no formation site, so its closed type is a law of its scheme. A template
binds each parameter to a part of an argument's type, and its answer is an instance at those
bindings. -/

namespace Ty

/-- **Each candidate's type is closed where the request is.** The walk of the match by bounds
gives a candidate the request's type at an occurrence, and that type is a part of the request.
The case list is the function's. A step of `closedSubst_matchArgsB`, its consumer, and so of the
claim `checked-types-closed`. It says nothing of the template. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_cands (v : Ty.Variance) (t r : Ty) (hr : r.closed = true) :
    ∀ c ∈ Bounds.cands v t r, c.2.2.closed = true := by
  revert hr
  induction v, t, r using Bounds.cands.induct_unfolding
      (motive_2 := fun _ _ _ _ rs result =>
        Ty.closedItems rs = true → ∀ c ∈ result, c.2.2.closed = true)
      (motive_3 := fun _ _ rs result =>
        Ty.closedItems rs = true → ∀ c ∈ result, c.2.2.closed = true)
      (motive_4 := fun _ _ gs result =>
        Ty.closedFields gs = true → ∀ c ∈ result, c.2.2.closed = true)
  case case1 =>
    intro h c hc
    rw [List.mem_singleton.mp hc]
    exact h
  case case2 ih | case3 ih | case4 ih | case5 ih => exact ih
  case case6 ih₁ ih₂ | case7 ih₁ ih₂ | case8 ih₁ ih₂ | case9 ih₁ ih₂ | case10 ih₁ ih₂
  | case11 ih₁ ih₂ | case12 ih₁ ih₂ =>
    intro h c hc
    have hp := Bool.and_eq_true_iff.mp h
    rcases List.mem_append.mp hc with hc | hc
    · exact ih₁ hp.1 c hc
    · exact ih₂ hp.2 c hc
  case case13 ih | case14 ih | case15 ih => exact ih
  case case16 => exact fun _ _ hc => nomatch hc
  case case17 ih₁ ih₂ =>
    intro h c hc
    have hp := Bool.and_eq_true_iff.mp h
    rcases List.mem_append.mp hc with hc | hc
    · exact ih₁ hp.1 c hc
    · exact ih₂ hp.2 c hc
  case case18 => exact fun _ _ hc => nomatch hc
  case case19 _ _ hc => exact nomatch hc
  case case20 ih h c hc => exact ih (Bool.and_eq_true_iff.mp h).2 c hc
  case case21 ih₂ ih₁ h c hc =>
    have hp := Bool.and_eq_true_iff.mp h
    rcases List.mem_append.mp hc with hc | hc
    · exact ih₂ hp.1 c hc
    · exact ih₁ hp.2 c hc
  case case22 ih₂ ih₁ h c hc =>
    have hp := Bool.and_eq_true_iff.mp h
    rw [Bounds.candsArgs] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih₂ hp.1 c hc
    · exact ih₁ hp.2 c hc
  case case23 other _ c hc =>
    rw [Bounds.candsArgs] at hc
    · exact nomatch hc
    · exact other
  case case24 ih₂ ih₁ h c hc =>
    have hp := Bool.and_eq_true_iff.mp h
    rw [Bounds.candsItems] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ih₂ hp.1 c hc
    · exact ih₁ hp.2 c hc
  case case25 other _ c hc =>
    rw [Bounds.candsItems] at hc
    · exact nomatch hc
    · exact other

/-- **The join of closed candidates is closed** (`UnionRule.closed_join`). A step of
`closedSubst_matchArgsB`, its consumer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_joinCands : ∀ (l : List Ty), (∀ c ∈ l, c.closed = true) →
    (Bounds.joinCands l).closed = true
  | [], _ => rfl
  | [x], h => h x List.mem_cons_self
  | x :: y :: rest, h =>
    UnionRule.closed_join (h x List.mem_cons_self)
      (closed_joinCands (y :: rest) fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- **A list match by bounds reads closed bindings from closed arguments.** Each binding is the
join of candidates (`closed_joinCands`), and each candidate is a part of an argument
(`closed_cands`). A step of `NativeAtom.Scheme.closed_apply`, its consumer, and so of the claim
`checked-types-closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closedSubst_matchArgsB {σ : Subst} {ps rs : List Ty}
    (h : Bounds.matchArgsB ps rs = some σ)
    (hrs : ∀ r ∈ rs, r.closed = true) : ClosedSubst σ := by
  have hcs : ∀ c ∈ Bounds.candsList ps rs, c.2.2.closed = true := by
    intro c hc
    obtain ⟨pr, hpr, hc⟩ := List.mem_flatMap.mp hc
    exact closed_cands .co pr.1 pr.2 (hrs pr.2 (List.of_mem_zip hpr).2) c hc
  unfold Bounds.matchArgsB at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      intro b hb
      obtain ⟨c, -, hb⟩ :=
        List.mem_filterMap.mp ((List.mem_append.mp hb).resolve_left (nomatch ·))
      split at hb
      · exact nomatch hb
      · cases hb
        refine closed_joinCands _ fun x hx => ?_
        unfold Bounds.lowers at hx
        obtain ⟨d, hd, hx⟩ := List.mem_filterMap.mp hx
        split at hx
        · cases hx
          exact hcs d hd
        · exact nomatch hx
    · exact nomatch h
  · exact nomatch h

end Ty

/-- A closed cause or exit type has a closed error type. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Member.cause_closed {m : Ty} {a : Ty} (closed : m.closed = true)
    (answered : Member.cause m = some a) : a.closed = true := by
  cases m with
  | causeOf e =>
    cases answered
    exact closed
  | exitOf v e =>
    cases answered
    exact (Bool.and_eq_true_iff.mp closed).2
  | _ => exact nomatch answered

/-- The error column of a cause or of an exit is closed when the type is. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_causeInputError {input error : Ty} (hi : input.closed = true)
    (h : causeInputError? input = some error) : error.closed = true :=
  UnionRule.extend_closed Member.cause_closed h hi

namespace NativeAtom

/-- The selected column of a closed product type is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_projectProduct {second : Bool} {t : Ty} : ∀ {r : Ty}, t.closed = true →
    projectProduct second t = some r → r.closed = true := by
  induction t with
  | prod a b _ _ =>
    intro r ht h
    cases h
    have hc := Bool.and_eq_true_iff.mp ht
    cases second
    · exact hc.1
    · exact hc.2
  | union a b iha ihb =>
    intro r ht h
    have hc := Bool.and_eq_true_iff.mp ht
    simp only [projectProduct, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, rr, hr, rfl⟩ := h
    exact UnionRule.closed_join (iha hc.1 hl) (ihb hc.2 hr)
  | never =>
    intro r _ h
    cases h
    rfl
  | _ => exact fun _ h => nomatch h

/-- A custom rule answers a closed type at closed arguments. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem CustomScheme.closed_apply (tag : CustomScheme) {tys : List Ty} {ty : Ty}
    (htys : ∀ t ∈ tys, t.closed = true) (h : tag.apply tys = some ty) : ty.closed = true := by
  cases tag with
  | project second =>
    rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact nomatch h
    · exact closed_projectProduct (htys a List.mem_cons_self) h
    · exact nomatch h
  | causeTest =>
    rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact nomatch h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · exact nomatch h
  | causeError =>
    rcases tys with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact nomatch h
    · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
      have he' : e.closed = true := closed_causeInputError (htys a List.mem_cons_self) he
      exact he'
    · exact nomatch h
  | tuple =>
    cases h
    refine Ty.closed_normalize _ ?_
    rw [Ty.closed, Ty.closedItems_eq_all, List.all_eq_true]
    exact htys
  | sameHandle =>
    have h' : sameHandleRule tys = some ty := h
    unfold sameHandleRule at h'
    split at h'
    · cases h'
      rfl
    · cases h'
      rfl
    · exact nomatch h'

/-- A fixed signature answers its declared answer. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_monoApply {params tys : List Ty} {answer ty : Ty} (ha : answer.closed = true)
    (h : monoApply params answer tys = some ty) : ty.closed = true := by
  unfold monoApply at h
  split at h
  · cases h
    exact ha
  · exact nomatch h

/-- The answers a scheme declares outright are closed. A template's answer is not asked: its
instance at closed bindings is closed (`Ty.closed_instantiate`). A custom rule declares none. -/
def Scheme.answersClosed : Scheme → Bool
  | .mono _ answer => answer.closed
  | .variadic _ answer => answer.closed
  | .alts cases => cases.all fun c => c.2.closed
  | .poly .. | .custom _ => true

/-- **A scheme answers a closed type at closed arguments**, when its declared answers are
closed. A step of `closedSig_native`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem Scheme.closed_apply (s : Scheme) (hs : s.answersClosed = true) {tys : List Ty} {ty : Ty}
    (htys : ∀ t ∈ tys, t.closed = true) (h : s.apply tys = some ty) : ty.closed = true := by
  cases s with
  | mono params answer => exact closed_monoApply hs h
  | variadic param answer =>
    simp only [Scheme.apply] at h
    split at h
    · cases h
      exact hs
    · exact nomatch h
  | poly params answer =>
    obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Ty.closed_instantiate
      (Ty.closedSubst_matchArgsB hσ htys) answer
  | alts cases =>
    obtain ⟨c, hc, hmono⟩ := List.exists_of_findSome?_eq_some h
    exact closed_monoApply (List.all_eq_true.mp hs c hc) hmono
  | custom tag => exact tag.closed_apply htys h

/-- Every atom's declared answers are closed: read off the table, atom by atom. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem spec_answersClosed (atom : NativeAtom) : (spec atom).scheme.answersClosed = true := by
  cases atom <;> rfl

/-- An atom answers a closed type at closed arguments. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_typeOf (atom : NativeAtom) {tys : List Ty} {ty : Ty}
    (htys : ∀ t ∈ tys, t.closed = true) (h : atom.typeOf tys = some ty) : ty.closed = true :=
  (spec atom).scheme.closed_apply (spec_answersClosed atom) htys h

end NativeAtom

/-! ## 3. The annotations of a program, as a fold

The collector is a path fold into lists. A proof that follows a program's shape wants a
conjunction over the node's parts. The two are one fold seen through a homomorphism: the law is
`foldMapAt_eff_fuse` (`Laws/Program/PathFold.lean`). -/

namespace Formation

/-- Every annotation in a list has a type that satisfies `P`: the homomorphism from the
collector's lists, under append, to propositions, under conjunction. -/
def allTypes (P : Ty → Prop) (l : List (List String × Ty)) : Prop := ∀ x ∈ l, P x.2

@[semantics "subtyping-algebra" (requirement := R14)]
theorem allTypes_append (P : Ty → Prop) (a b : List (List String × Ty)) :
    allTypes P (a ++ b) = (allTypes P a ∧ allTypes P b) :=
  propext List.forall_mem_append

@[semantics "subtyping-algebra" (requirement := R14)]
theorem allTypes_nil (P : Ty → Prop) : allTypes P [] = True :=
  propext ⟨fun _ => trivial, fun _ _ hx => nomatch hx⟩

@[semantics "subtyping-algebra" (requirement := R14)]
theorem allTypes_singleton (P : Ty → Prop) (path : List String) (ty : Ty) :
    allTypes P [(path, ty)] = P ty :=
  propext ⟨fun h => h (path, ty) List.mem_cons_self,
    fun h x hx => by rw [List.mem_singleton.mp hx]; exact h⟩

/-- A property of each member of an option, at `none`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem forall_mem_none {α : Type} (p : α → Prop) :
    (∀ x ∈ (none : Option α), p x) = True :=
  propext ⟨fun _ => trivial, fun _ _ hx => nomatch Option.mem_def.mp hx⟩

/-- A property of each member of an option, at `some`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem forall_mem_some {α : Type} (p : α → Prop) (a : α) : (∀ x ∈ some a, p x) = p a :=
  propext ⟨fun h => h a rfl, fun h _ hx => Option.some.inj (Option.mem_def.mp hx) ▸ h⟩

/-- What one term node states: a record's declaration, and a list fold's stated accumulator.
`termAnnotations` collects the same two. -/
def termNodeAll (P : Ty → Prop) : Term → Prop
  | .record fields _ _ => P (.record fields)
  | .fold (some accTy) _ _ _ => P accTy
  | _ => True

/-- Every type that a term states satisfies `P`, as a fold of the term. -/
def TermAll (P : Ty → Prop) (t : Term) : Prop :=
  foldMap_term True And t (termNodeAll P) (fun _ => True)

/-- Every type that an argument list states satisfies `P`. -/
def TermsAll (P : Ty → Prop) (ts : Terms) : Prop :=
  foldMap_terms True And ts (termNodeAll P) (fun _ => True)

/-- **The annotations of a term, as a fold**: every annotation's type satisfies `P` exactly when
the term's fold does, at every path. A step of `programAnnotations_all`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem termAnnotations_all (P : Ty → Prop) (path : List String) (t : Term) :
    allTypes P (termAnnotations path t) = TermAll P t := by
  unfold termAnnotations TermAll
  refine foldMapAt_term_fuse (allTypes P) (allTypes_append P) (fun n q => ?_)
    (fun _ _ => allTypes_nil P) t []
  cases n with
  | record fields names values => exact allTypes_singleton P _ _
  | fold accTy list init body =>
    cases accTy with
    | none => exact allTypes_nil P
    | some accTy => exact allTypes_singleton P _ _
  | _ => exact allTypes_nil P

/-- The annotations of an optional term. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem optionTerm_all (P : Ty → Prop) (path : List String) (t : Option Term) :
    allTypes P (t.toList.flatMap (termAnnotations path)) = ∀ x ∈ t, TermAll P x := by
  cases t with
  | none => exact (allTypes_nil P).trans (forall_mem_none _).symm
  | some x =>
    show allTypes P (termAnnotations path x ++ []) = _
    rw [List.append_nil, termAnnotations_all, forall_mem_some]

/-- Every type that a cause's terms state satisfies `P`, as a fold of the cause. -/
def CauseAll (P : Ty → Prop) : CauseTerm → Prop :=
  cata_cause (R := fun _ => Prop)
    { cause_fail := TermAll P
      cause_die := TermAll P
      cause_interrupt := fun who => ∀ t ∈ who, TermAll P t
      cause_both := And }

/-- The annotations of a cause, as a fold. A step of `programAnnotations_all`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem causeAnnotations_all (P : Ty → Prop) (c : CauseTerm) :
    ∀ path : List String, allTypes P (causeAnnotations path c) = CauseAll P c := by
  induction c with
  | fail term => exact fun path => termAnnotations_all P _ term
  | die term => exact fun path => termAnnotations_all P _ term
  | interrupt who => exact fun path => optionTerm_all P _ who
  | both left right ihl ihr =>
    intro path
    show allTypes P (causeAnnotations (path ++ ["left"]) left ++
      causeAnnotations (path ++ ["right"]) right) = (CauseAll P left ∧ CauseAll P right)
    rw [allTypes_append, ihl, ihr]

/-- The types a list states at its positions, whatever path each is filed under. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem allTypes_zipIdx_map (P : Ty → Prop) (tys : List Ty) (f : Ty × Nat → List String × Ty)
    (hf : ∀ x, (f x).2 = x.1) : allTypes P (tys.zipIdx.map f) = ∀ t ∈ tys, P t := by
  refine propext ⟨fun h t ht => ?_, fun h x hx => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
    have hmem : (t, i) ∈ tys.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    have := h (f (t, i)) (List.mem_map_of_mem hmem)
    rw [hf] at this
    exact this
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hf]
    exact h y.1 (List.fst_mem_of_mem_zipIdx hy)

variable {Op : Type} [ScopedOp Op]

/-- What one argument of a node states. A term and a cause state what their folds state. A
loop's cursor type is stated as it is. An operation states its binder term's types and its type
arguments. A child is a node of its own, and every other argument states nothing. -/
def ArgAll (P : Ty → Prop) : ArgF Op (EffSelfCarrier Op) → Prop
  | .term t => TermAll P t
  | .cause c => CauseAll P c
  | .optTerm t => ∀ x ∈ t, TermAll P x
  | .optTy ty => ∀ t ∈ ty, P t
  | .op op => (∀ t ∈ ScopedOp.term? op, TermAll P t) ∧ ∀ t ∈ ScopedOp.typeArgs op, P t
  | .decls ds => ∀ d ∈ ds, P d.request ∧ P d.answer ∧ P d.error
  | _ => True

/-- The declared columns of a definition block, as `ArgAll`. A step of
`argumentAnnotations_all`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem declAnnotations_all (P : Ty → Prop) (path : List String) (ds : List DefDecl) :
    allTypes P (Formation.declAnnotations path ds) =
      ∀ d ∈ ds, P d.request ∧ P d.answer ∧ P d.error := by
  refine propext ⟨fun h d hd => ?_, fun h x hx => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    have hmem : (d, i) ∈ ds.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    have hsub : ∀ y ∈ [(path ++ [toString i, "request"], d.request),
        (path ++ [toString i, "answer"], d.answer), (path ++ [toString i, "error"], d.error)],
        P y.2 := fun y hy => h y (List.mem_flatMap.mpr ⟨(d, i), hmem, hy⟩)
    exact ⟨hsub _ List.mem_cons_self, hsub _ (List.mem_cons_of_mem _ List.mem_cons_self),
      hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  · obtain ⟨⟨d, i⟩, hmem, hx⟩ := List.mem_flatMap.mp hx
    have hd : d ∈ ds := List.mem_iff_getElem?.mpr ⟨i, List.mem_zipIdx_iff_getElem?.mp hmem⟩
    obtain ⟨hr, ha, he⟩ := h d hd
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hr
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he
    exact nomatch hx

/-- The annotations of one argument, as `ArgAll`. A step of `nodeAnnotations_all`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem argumentAnnotations_all (P : Ty → Prop) (path : List String) (index : Nat)
    (arg : ArgF Op (EffSelfCarrier Op)) :
    allTypes P (argumentAnnotations path index arg) = ArgAll P arg := by
  cases arg with
  | term t => exact termAnnotations_all P _ t
  | cause c => exact causeAnnotations_all P c _
  | optTerm t => exact optionTerm_all P _ t
  | optTy ty =>
    cases ty with
    | none => exact (allTypes_nil P).trans (forall_mem_none _).symm
    | some t => exact (allTypes_singleton P _ t).trans (forall_mem_some _ t).symm
  | op op =>
    refine (allTypes_append P _ _).trans ?_
    refine congr (congrArg And (optionTerm_all P _ _)) (allTypes_zipIdx_map P _ _ ?_)
    exact fun _ => rfl
  | decls ds => exact declAnnotations_all P _ ds
  | _ => exact allTypes_nil P

/-- What a node's own arguments state, in order: a conjunction over the node's view. -/
def ArgsAll (P : Ty → Prop) : List (ArgF Op (EffSelfCarrier Op)) → Prop
  | [] => True
  | arg :: rest => ArgAll P arg ∧ ArgsAll P rest

/-- What one node states by itself: its arguments, read through the generated view. -/
def NodeAll (P : Ty → Prop) (fam : EffFam) (node : EffSelfCarrier Op fam) : Prop :=
  ArgsAll P (view fam node).2

/-- The annotations of an argument list, as `ArgsAll`. A step of `nodeAnnotations_all`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem argsAnnotations_all (P : Ty → Prop)
    (f : ArgF Op (EffSelfCarrier Op) × Nat → List (List String × Ty))
    (hf : ∀ x, allTypes P (f x) = ArgAll P x.1) :
    ∀ (args : List (ArgF Op (EffSelfCarrier Op))) (k : Nat),
      allTypes P ((args.zipIdx k).flatMap f) = ArgsAll P args
  | [], _ => allTypes_nil P
  | arg :: rest, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, allTypes_append, hf,
      argsAnnotations_all P f hf rest (k + 1)]
    rfl

/-- The annotations of one node, as `NodeAll`, at every path. A step of
`programAnnotations_all`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem nodeAnnotations_all (P : Ty → Prop) (fam : EffFam) (node : EffSelfCarrier Op fam)
    (path : List Nat) : allTypes P (nodeAnnotations fam node path) = NodeAll P fam node :=
  argsAnnotations_all P _ (fun ⟨arg, index⟩ => argumentAnnotations_all P _ index arg)
    (view fam node).2 0

/-- The fold of `NodeAll` with no path, at a program: `AnnotationsAll` at this sort. -/
abbrev effAll (P : Ty → Prop) (node : Eff Op) : Prop :=
  foldMap_eff True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- The fold of `NodeAll` with no path, at a statement: `AnnotationsAll` at this sort. -/
abbrev stmtAll (P : Ty → Prop) (node : Stmt Op) : Prop :=
  foldMap_stmt True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- The fold of `NodeAll` with no path, at a statement list: `AnnotationsAll` at this sort. -/
abbrev stmtsAll (P : Ty → Prop) (node : Stmts Op) : Prop :=
  foldMap_stmts True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- The fold of `NodeAll` with no path, at a race's entrants: `AnnotationsAll` at this sort. -/
abbrev effsAll (P : Ty → Prop) (node : Effs Op) : Prop :=
  foldMap_effs True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- The fold of `NodeAll` with no path, at a fiber action: `AnnotationsAll` at this sort. -/
abbrev actionAll (P : Ty → Prop) (node : ActionTerm Op) : Prop :=
  foldMap_action True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- The fold of `NodeAll` with no path, at a layer: `AnnotationsAll` at this sort. -/
abbrev layerAll (P : Ty → Prop) (node : LayerTerm Op) : Prop :=
  foldMap_layer True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- The fold of `NodeAll` with no path, at a layer list: `AnnotationsAll` at this sort. -/
abbrev layersAll (P : Ty → Prop) (node : LayerTerms Op) : Prop :=
  foldMap_layers True And node (NodeAll P .eff) (NodeAll P .stmt) (NodeAll P .stmts)
    (NodeAll P .effs) (NodeAll P .action) (NodeAll P .layer) (NodeAll P .layers)

/-- **Every annotation under a node of the program's family has a type that satisfies `P`**, as
a fold of the node: a conjunction that follows the node's shape. At a program it is the fold
form of `programAnnotations` (`programAnnotations_all`). A proof by rule induction reads its
premise at each rule by projections. -/
def AnnotationsAll (P : Ty → Prop) : (fam : EffFam) → EffSelfCarrier Op fam → Prop
  | .eff => effAll P
  | .stmt => stmtAll P
  | .stmts => stmtsAll P
  | .effs => effsAll P
  | .action => actionAll P
  | .layer => layerAll P
  | .layers => layersAll P

/-- **The annotations of a program, as a fold**: every annotation's type satisfies `P` exactly
when the program's fold does. The collector reads each node through the generated view, and so
does `NodeAll`: no constructor of the program's family is named. A step of `check_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem programAnnotations_all (P : Ty → Prop) (e : Eff Op) :
    allTypes P (programAnnotations e) ↔ AnnotationsAll P .eff e :=
  Iff.of_eq (foldMapAt_eff_fuse (allTypes P) (allTypes_append P) (nodeAnnotations_all P) e [])

/-- Every annotation under a node has a closed type. -/
abbrev AnnotationsClosed (fam : EffFam) (node : EffSelfCarrier Op fam) : Prop :=
  AnnotationsAll (fun t => t.closed = true) fam node

/-- A program whose annotations are formed states closed types only, in the fold's form. A step
of `check_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem annotationsClosed_of_formed {e : Eff Op} (h : Formed (programSites e)) :
    AnnotationsClosed .eff e :=
  (programAnnotations_all _ e).mp (annotations_closed h)

/-! ### Layer references

The whole-program checker types a program's expansion (`typeOfProgram`,
`Program/Typing.lean`): each layer reference is replaced by the layer at its target. Formation
reads the program as it is stored. An expansion states nothing that the program does not
state, so the formation premise of the stored program serves its expansion. -/

mutual

/-- **A substitution of the layer references keeps the annotations' fold**, when each substitute
satisfies it. A reference states nothing, a substitute states what its fold says, and no other
node's own arguments change. The statement is on the generated folds, one per sort, each proved
by the sort's own case list. Its consumer is `annotationsAll_expandRefs`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem effAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : Eff Op) :
    effAll P (cata_eff (refAlgebra f) node) = effAll P node := by
  cases node <;> simp only [effAll, cata_eff, EffAlgebra.id, foldMap_eff, NodeAll, view, view_eff,
    ArgsAll, ArgAll, effAll_onRef P f hf, stmtsAll_onRef P f hf, effsAll_onRef P f hf,
    actionAll_onRef P f hf, layerAll_onRef P f hf]

/-- `effAll_onRef` at a statement. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem stmtAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : Stmt Op) :
    stmtAll P (cata_stmt (refAlgebra f) node) = stmtAll P node := by
  cases node <;> simp only [stmtAll, cata_stmt, EffAlgebra.id, foldMap_stmt, NodeAll, view,
    view_stmt, ArgsAll, ArgAll, effAll_onRef P f hf, stmtsAll_onRef P f hf]

/-- `effAll_onRef` at a statement list. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem stmtsAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : Stmts Op) :
    stmtsAll P (cata_stmts (refAlgebra f) node) = stmtsAll P node := by
  cases node <;> simp only [stmtsAll, cata_stmts, EffAlgebra.id, foldMap_stmts, NodeAll, view,
    view_stmts, ArgsAll, ArgAll, stmtAll_onRef P f hf, stmtsAll_onRef P f hf]

/-- `effAll_onRef` at a race's entrants. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem effsAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : Effs Op) :
    effsAll P (cata_effs (refAlgebra f) node) = effsAll P node := by
  cases node <;> simp only [effsAll, cata_effs, EffAlgebra.id, foldMap_effs, NodeAll, view,
    view_effs, ArgsAll, ArgAll, effAll_onRef P f hf, effsAll_onRef P f hf]

/-- `effAll_onRef` at a fiber action. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem actionAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : ActionTerm Op) :
    actionAll P (cata_action (refAlgebra f) node) = actionAll P node := by
  cases node <;> simp only [actionAll, cata_action, EffAlgebra.id, foldMap_action, NodeAll, view,
    view_action, ArgsAll, ArgAll, effAll_onRef P f hf, effsAll_onRef P f hf]

/-- `effAll_onRef` at a layer, the one sort with a reference: the substitute stands there. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem layerAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : LayerTerm Op) :
    layerAll P (cata_layer (refAlgebra f) node) = layerAll P node := by
  cases node <;> simp only [layerAll, cata_layer, EffAlgebra.id, foldMap_layer, NodeAll, view,
    view_layer, ArgsAll, ArgAll, and_self, hf, effAll_onRef P f hf, layerAll_onRef P f hf,
    layersAll_onRef P f hf]

/-- `effAll_onRef` at a layer list. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem layersAll_onRef (P : Ty → Prop) (f : List Nat → LayerTerm Op)
    (hf : ∀ target, layerAll P (f target) = True) (node : LayerTerms Op) :
    layersAll P (cata_layers (refAlgebra f) node) = layersAll P node := by
  cases node <;> simp only [layersAll, cata_layers, EffAlgebra.id, foldMap_layers, NodeAll, view,
    view_layers, ArgsAll, ArgAll, layerAll_onRef P f hf, layersAll_onRef P f hf]

end

/-- The collector's node functions as a path yield, so that the laws of the path folds
(`Laws/Program/PathFold.lean`) read the collector. -/
def annotationYield : PathYield Op (List String × Ty) where
  eff := nodeAnnotations .eff
  stmt := nodeAnnotations .stmt
  stmts := nodeAnnotations .stmts
  effs := nodeAnnotations .effs
  action := nodeAnnotations .action
  layer := nodeAnnotations .layer
  layers := nodeAnnotations .layers

/-- **The layer at a path of a program states what the program states there.** The path fold
collects every addressed node's fold (`Node.foldList_subset_of_at`), and the layer's path fold
is its fold with no path (`foldMapAt_layer_fuse`). A step of `annotationsAll_expandRefs`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem layerAll_of_layerAt (P : Ty → Prop) {root : Eff Op} {target : List Nat}
    {layer : LayerTerm Op} (h : (Node.eff root).layerAt target = some layer)
    (hroot : allTypes P (programAnnotations root)) : layerAll P layer := by
  have hat := (Node.layerAt_eq_some_iff _ _ _).mp h
  have hsub := Node.foldList_subset_of_at annotationYield target (.eff root) (.layer layer) [] hat
  rw [List.nil_append] at hsub
  exact (foldMapAt_layer_fuse (allTypes P) (allTypes_append P) (nodeAnnotations_all P) layer
    target).mp fun x hx => hroot x (hsub hx)

/-- **A program's expansion states what the program states.** Each round replaces a reference
by the layer at its target in the stored program, and that layer's annotations are the
program's (`layerAll_of_layerAt`). So each round keeps the fold (`effAll_onRef`). No premise is
asked of the references. A step of `typeOfProgram_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem annotationsAll_expandRefs (P : Ty → Prop) (root : Eff Op)
    (h : AnnotationsAll P .eff root) : AnnotationsAll P .eff root.expandRefs := by
  have hroot : allTypes P (programAnnotations root) := (programAnnotations_all P root).mpr h
  have hf : ∀ target,
      layerAll P (((Node.eff root).layerAt target).getD (.ref target)) = True := by
    intro target
    refine eq_true ?_
    cases hl : (Node.eff root).layerAt target with
    | none => exact ⟨trivial, trivial⟩
    | some layer => exact layerAll_of_layerAt P hl hroot
  have step : ∀ (rounds : List Nat) (acc : Eff Op), effAll P acc →
      effAll P (rounds.foldl (fun acc _ => Eff.expandRound (.eff root) acc) acc) := by
    intro rounds
    induction rounds with
    | nil => exact fun _ hacc => hacc
    | cons _ rounds ih => exact fun acc hacc => ih _ ((effAll_onRef P _ hf acc).mpr hacc)
  exact step _ root h

end Formation

/-! ## 4. Terms and causes -/

/-- **What the closed types of the checker ask of a signature**: an atom answers a closed type
at closed arguments, and every service carrier is closed. An atom's scheme and a carrier are no
formation sites of a program, so the two are premises. Nothing is asked of a row: the row rule
checks strict formation of each instantiated column (`closed_rowTy`). The native signature has
both (`closedSig_native`). -/
structure ClosedSig {Op : Type} (sig : Signature Op) : Prop where
  /-- An atom answers a closed type at closed arguments. -/
  atom : ∀ (name : String) (tys : List Ty) (ty : Ty), sig.atomOf name tys = some ty →
    (∀ t ∈ tys, t.closed = true) → ty.closed = true
  /-- Every service carrier is closed. -/
  service : ∀ (key : ServiceKey) (ty : Ty), sig.serviceTy key = some ty → ty.closed = true

/-- An environment of closed types. -/
def ClosedEnv (env : TyEnv) : Prop := ∀ t ∈ env, t.closed = true

@[semantics "subtyping-algebra" (requirement := R14)]
theorem ClosedEnv.nil : ClosedEnv [] := fun _ h => nomatch h

/-- An environment extended by closed types. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem ClosedEnv.append {env ext : TyEnv} (h : ClosedEnv env)
    (hext : ∀ t ∈ ext, t.closed = true) : ClosedEnv (env ++ ext) :=
  List.forall_mem_append.mpr ⟨h, hext⟩

/-- An environment extended by one closed type. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem ClosedEnv.push {env : TyEnv} {t : Ty} (h : ClosedEnv env) (ht : t.closed = true) :
    ClosedEnv (env ++ [t]) :=
  h.append (List.forall_mem_singleton.mpr ht)

/-- A stated type, or the type it stands in for, is closed when both are. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_getD {stated : Option Ty} {inferred : Ty}
    (hs : ∀ t ∈ stated, t.closed = true) (hi : inferred.closed = true) :
    (stated.getD inferred).closed = true := by
  cases stated with
  | none => exact hi
  | some t => exact hs t rfl

/-- The literal rule answers a closed type. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_litArgTy (const : Bool) (value : Lit) : (litArgTy const value).closed = true := by
  cases value <;> cases const <;> rfl

section Terms

variable {Op : Type} {sig : Signature Op}

mutual

/-- **A term's type is closed**, at a closed signature and environment, when the types the term
states are. A variable has the environment's type, an atom's answer is the signature's, and a
record's declaration is checked by the term typer itself. A list fold's type is its accumulator's:
the stated one, or the initial value's. A step of `hasTy_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem argTy_closed (hsig : ClosedSig sig) {env : TyEnv} (henv : ClosedEnv env) :
    ∀ (const : Bool) (t : Term) {ty : Ty}, Formation.TermAll (fun t => t.closed = true) t →
      argTy sig env const t = some ty → ty.closed = true
  | _, .var _, ty, _, h => henv ty (List.mem_of_getElem? h)
  | const, .lit value, _, _, h => by
    cases h
    exact closed_litArgTy const value
  | _, .app atom args, ty, hs, h => by
    simp only [argTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨tys, htys, hatom⟩ := h
    exact hsig.atom atom tys ty hatom (argsTy_closed hsig henv _ args hs.2 htys)
  | _, .record fields names values, _, _, h => by
    simp only [argTy] at h
    split at h
    · exact nomatch h
    · rename_i hformed
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, hrecord⟩ := h
      exact Record.closed_check
        (Formation.closed_of_formed ((Formation.check_eq_none_iff _).mp hformed)) hrecord
  | _, .field mode target name, _, hs, h => by
    simp only [argTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨type, htarget, hfield⟩ := h
    exact Record.closed_fieldType (argTy_closed hsig henv false target hs.2 htarget) hfield
  | _, .recordSet target name value, _, hs, h => by
    simp only [argTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨targetType, htarget, valueType, hvalue, hset⟩ := h
    exact Record.closed_setType (argTy_closed hsig henv false target hs.2.1 htarget)
      (argTy_closed hsig henv true value hs.2.2 hvalue) hset
  | _, .tupleAt target index, _, hs, h => by
    simp only [argTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨targetType, htarget, hat⟩ := h
    exact Tuple.closed_typeAt (argTy_closed hsig henv false target hs.2 htarget) hat
  | _, .fold accTy list init body, ty, hs, h => by
    simp only [argTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, initType, hinit, h⟩ := h
    have hacc : (accTy.getD initType).closed = true := by
      cases accTy with
      | none => exact argTy_closed hsig henv false init hs.2.2.1 hinit
      | some stated => exact hs.1
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · cases h
        exact hacc
      · exact nomatch h
    · exact nomatch h

/-- `argTy_closed` at an argument list. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem argsTy_closed (hsig : ClosedSig sig) {env : TyEnv} (henv : ClosedEnv env) :
    ∀ (const : Bool) (ts : Terms) {tys : List Ty},
      Formation.TermsAll (fun t => t.closed = true) ts → argsTy sig env const ts = some tys →
      ∀ t ∈ tys, t.closed = true
  | _, .nil, _, _, h => by
    cases h
    exact fun _ ht => nomatch ht
  | const, .cons head tail, _, hs, h => by
    rw [argsTy_cons] at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t, ht, rest, hrest, rfl⟩ := h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact argTy_closed hsig henv const head hs.2.1 ht
    · exact argsTy_closed hsig henv const tail hs.2.2 hrest u hu

end

/-- A term's type is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem termTy_closed (hsig : ClosedSig sig) {env : TyEnv} (henv : ClosedEnv env) {t : Term}
    {ty : Ty} (hs : Formation.TermAll (fun t => t.closed = true) t)
    (h : termTy sig env t = some ty) : ty.closed = true :=
  argTy_closed hsig henv false t hs h

/-- A cause's error type is closed. A step of `hasTy_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem causeTy_closed (hsig : ClosedSig sig) {env : TyEnv} (henv : ClosedEnv env)
    (c : CauseTerm) : ∀ {ty : Ty}, Formation.CauseAll (fun t => t.closed = true) c →
      causeTy sig env c = some ty → ty.closed = true := by
  induction c with
  | fail error =>
    intro ty hs h
    simp only [causeTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, he, h⟩ := h
    split at h
    · cases h
      exact termTy_closed hsig henv hs he
    · exact nomatch h
  | die defect =>
    intro ty _ h
    simp only [causeTy, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    split at h
    · cases h
      rfl
    · exact nomatch h
  | interrupt who =>
    intro ty _ h
    cases who with
    | none =>
      cases h
      rfl
    | some who =>
      simp only [causeTy, bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · cases h
        rfl
      · exact nomatch h
  | both left right ihl ihr =>
    intro ty hs h
    simp only [causeTy, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨l, hl, r, hr, rfl⟩ := h
    exact UnionRule.closed_join (ihl hs.1 hl) (ihr hs.2 hr)

end Terms

/-! ## 5. The six judgments -/

/-- An effect type whose answer and error are closed. The requirement row holds keys, and no
type. -/
def EffTy.Closed (t : EffTy) : Prop := t.answer.closed = true ∧ t.error.closed = true

/-- A generator state whose answer, when it has one, and whose error are closed. -/
def GenTy.Closed (g : GenTy) : Prop :=
  (∀ a ∈ g.answer, a.closed = true) ∧ g.error.closed = true

/-- **The row rule answers closed types, with no premise.** A checked row use has checked strict
formation of each instantiated column, and strict formation gives a closed type
(`Formation.closed_of_formed`). So nothing is asked of the row, of the request or of the
operation's binder term. A step of `hasTy_closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_rowTy {row : Row} {request : Ty} {use : Option TermUse} {t : EffTy}
    (h : rowTy row request use = some t) : t.Closed := by
  rw [rowTy_eq_some_iff] at h
  unfold checkRow at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hformed
        cases h
        have formed := (Formation.check_eq_none_iff _).mp hformed
        exact ⟨Ty.closed_normalize _ (Formation.closed_of_formed fun site hsite =>
            formed site (List.mem_append_left _ (List.mem_append_right _ hsite))),
          Ty.closed_normalize _ (Formation.closed_of_formed fun site hsite =>
            formed site (List.mem_append_right _ hsite))⟩

/-- The joined answer of two closed answers is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_joinAnswer {a b answer : Ty} (h : EffTy.joinAnswer a b = some answer)
    (ha : a.closed = true) (hb : b.closed = true) : answer.closed = true := by
  cases h
  exact UnionRule.closed_join ha hb

namespace GenTy

/-- The joined answer of two generator states. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_joinAnswerT {a b : Option Ty} (ha : ∀ x ∈ a, x.closed = true)
    (hb : ∀ x ∈ b, x.closed = true) : ∀ x ∈ joinAnswerT a b, x.closed = true := by
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      intro x hx
      rw [← Option.some.inj (Option.mem_def.mp hx)]
      exact UnionRule.closed_join (ha a rfl) (hb b rfl)

/-- An `if`'s merged state is closed when both branches' are. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_merge {a b ab : GenTy} (h : merge a b = some ab) (ha : a.Closed) (hb : b.Closed) :
    ab.Closed := by
  rw [merge_eq] at h
  cases h
  exact ⟨closed_joinAnswerT ha.1 hb.1, UnionRule.closed_join ha.2 hb.2⟩

/-- A statement's state before its tail's is closed when both are. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_seq {s r g : GenTy} (h : seq s r = some g) (hs : s.Closed) (hr : r.Closed) :
    g.Closed := by
  rw [seq_eq] at h
  cases h
  exact ⟨closed_joinAnswerT hs.1 hr.1, UnionRule.closed_join hs.2 hr.2⟩

/-- The answer of a generator over a closed state is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_genAnswer {g : GenTy} (hg : g.Closed) : g.genAnswer.closed = true := by
  unfold genAnswer
  split
  · rfl
  · rename_i t hanswer
    have ht : t.closed = true := hg.1 t hanswer
    split
    · exact UnionRule.closed_join ht rfl
    · exact ht

end GenTy

section Judgments

variable {Op : Type} [ScopedOp Op] {sig : Signature Op}

open Formation (AnnotationsClosed)

mutual

/-- **A typed program has closed types**, at a closed signature and environment, when its
annotations state closed types. One line per rule of `HasTy`: each rule builds its type from its
children's types by operations that keep closed types closed. The annotation premise is read at
a loop's cursor type and inside a term, and nowhere else. The claim `checked-types-closed`, at
the judgment. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem hasTy_closed (hsig : ClosedSig sig) :
    ∀ {env : TyEnv} {e : Eff Op} {t : EffTy}, HasTy sig env e t → ClosedEnv env →
      AnnotationsClosed .eff e → t.Closed
  | _, _, _, .succeed ht, henv, hs => ⟨termTy_closed hsig henv hs.1 ht, rfl⟩
  | _, _, _, .fail ht _, henv, hs => ⟨rfl, termTy_closed hsig henv hs.1 ht⟩
  | _, _, _, .failCause hc, henv, hs => ⟨rfl, causeTy_closed hsig henv _ hs.1 hc⟩
  | _, _, _, .sync ht, henv, hs => ⟨termTy_closed hsig henv hs.1 ht, rfl⟩
  | _, _, _, .suspend hb, henv, hs => hasTy_closed hsig hb henv hs.2
  | _, _, _, .perform _ _ hrow, _, _ => closed_rowTy hrow
  | _, _, _, .bind hf hr, henv, hs =>
    have f := hasTy_closed hsig hf henv hs.2.1
    have r := hasTy_closed hsig hr (henv.push f.1) hs.2.2
    ⟨r.1, UnionRule.closed_join f.2 r.2⟩
  | _, _, _, .gen hb, henv, hs =>
    have g := stmtsHasTy_closed hsig hb henv hs.2
    ⟨GenTy.closed_genAnswer g, g.2⟩
  | _, _, _, .catchCause hb hh hj, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2.1
    have h := hasTy_closed hsig hh (henv.push b.2) hs.2.2
    ⟨closed_joinAnswer hj b.1 h.1, h.2⟩
  | _, _, _, .catchIf hb _ _ hh hj, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2.1
    have h := hasTy_closed hsig hh (henv.push b.2) hs.2.2
    ⟨closed_joinAnswer hj b.1 h.1, closed_catchIfError _ _ b.2 h.2⟩
  | _, _, _, .select ht hd h0 h1 hj, henv, hs =>
    have arms := Decision.closed_arms (termTy_closed hsig henv hs.1.1 ht) hd
    have t0 := hasTy_closed hsig h0 (henv.append arms.1) hs.2.1
    have t1 := hasTy_closed hsig h1 (henv.append arms.2) hs.2.2
    ⟨closed_joinAnswer hj t0.1 t1.1, UnionRule.closed_join t0.2 t1.2⟩
  | _, _, _, .matchCause hb hv hc hj, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2.1
    have v := hasTy_closed hsig hv (henv.push b.1) hs.2.2.1
    have c := hasTy_closed hsig hc (henv.push b.2) hs.2.2.2
    ⟨closed_joinAnswer hj v.1 c.1, UnionRule.closed_join v.2 c.2⟩
  | _, _, _, .onExit hb hf, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2.1
    have f := hasTy_closed hsig hf (henv.push (Bool.and_eq_true_iff.mpr b)) hs.2.2
    ⟨b.1, UnionRule.closed_join b.2 f.2⟩
  | _, _, _, .exit hb, henv, hs =>
    ⟨Bool.and_eq_true_iff.mpr (hasTy_closed hsig hb henv hs.2), rfl⟩
  | _, _, _, .uninterruptible hb, henv, hs => hasTy_closed hsig hb henv hs.2
  | _, _, _, .interruptible hb, henv, hs => hasTy_closed hsig hb henv hs.2
  | _, _, _, .iterate hi _ _ hb _ hr _ _, henv, hs =>
    have cursor := closed_getD hs.1.1 (termTy_closed hsig henv hs.1.2.1 hi)
    have b := hasTy_closed hsig hb (henv.push cursor) hs.2
    ⟨termTy_closed hsig (henv.push cursor) hs.1.2.2.2.2.1 hr, b.2⟩
  | _, _, _, .yieldNow _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .awaitFiber_join ht hf, henv, hs =>
    closed_fiberTy (termTy_closed hsig henv hs.1 ht) hf
  | _, _, _, .awaitFiber_await ht hf, henv, hs =>
    ⟨Bool.and_eq_true_iff.mpr (closed_fiberTy (termTy_closed hsig henv hs.1 ht) hf), rfl⟩
  | _, _, _, .withFiber ha, henv, hs => actionHasTy_closed hsig ha henv hs.2
  | _, _, _, .scoped hb, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2
    ⟨b.1, b.2⟩
  | _, _, _, .acquireRelease ha _ _, henv, hs =>
    have a := hasTy_closed hsig ha henv hs.2.1
    ⟨a.1, a.2⟩
  | _, _, _, .provideLayer _ hl hb, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2.2
    ⟨b.1, UnionRule.closed_join b.2 (layerHasTy_closed hsig hl hs.2.1)⟩
  | _, _, _, .service hk, _, _ => ⟨hsig.service _ _ hk, rfl⟩
  | _, _, _, .provideService _ _ _ hb, henv, hs =>
    have b := hasTy_closed hsig hb henv hs.2
    ⟨b.1, b.2⟩
  | _, _, _, .restore _ _ hb, henv, hs => hasTy_closed hsig hb henv hs.2

/-- A generator body leaves a closed state. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem stmtsHasTy_closed (hsig : ClosedSig sig) :
    ∀ {env : TyEnv} {inLoop : Bool} {b : Stmts Op} {g : GenTy}, StmtsHasTy sig env inLoop b g →
      ClosedEnv env → AnnotationsClosed .stmts b → g.Closed
  | _, _, _, _, .nil, _, _ => ⟨fun _ h => (nomatch Option.mem_def.mp h), rfl⟩
  | _, _, _, _, .bindYield he hr, henv, hs =>
    have t := hasTy_closed hsig he henv hs.2.1.2
    have r := stmtsHasTy_closed hsig hr (henv.push t.1) hs.2.2
    ⟨r.1, UnionRule.closed_join t.2 r.2⟩
  | _, _, _, _, .yieldDiscard he hr, henv, hs =>
    have t := hasTy_closed hsig he henv hs.2.1.2
    have r := stmtsHasTy_closed hsig hr henv hs.2.2
    ⟨r.1, UnionRule.closed_join t.2 r.2⟩
  | _, _, _, _, .ret ht, henv, hs =>
    ⟨fun _ ha => Option.some.inj (Option.mem_def.mp ha) ▸ termTy_closed hsig henv hs.2.1.1 ht,
      rfl⟩
  | _, _, _, _, .ifElse _ _ ha hb hr hab hg, henv, hs =>
    GenTy.closed_seq hg
      (GenTy.closed_merge hab (stmtsHasTy_closed hsig ha henv hs.2.1.2.1)
        (stmtsHasTy_closed hsig hb henv hs.2.1.2.2))
      (stmtsHasTy_closed hsig hr henv hs.2.2)
  | _, _, _, _, .whileTrue hb hr hg, henv, hs =>
    have b := stmtsHasTy_closed hsig hb henv hs.2.1.2
    GenTy.closed_seq hg ⟨b.1, b.2⟩ (stmtsHasTy_closed hsig hr henv hs.2.2)
  | _, _, _, _, .breakLoop hr, henv, hs =>
    have g := stmtsHasTy_closed hsig hr henv hs.2.2
    ⟨g.1, g.2⟩

/-- A race's entrants have closed types. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem effsHasTy_closed (hsig : ClosedSig sig) :
    ∀ {env : TyEnv} {es : Effs Op} {t : EffTy}, EffsHasTy sig env es t → ClosedEnv env →
      AnnotationsClosed .effs es → t.Closed
  | _, _, _, .nil, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .cons hh ht hj, henv, hs =>
    have h := hasTy_closed hsig hh henv hs.2.1
    have t := effsHasTy_closed hsig ht henv hs.2.2
    ⟨closed_joinAnswer hj h.1 t.1, UnionRule.closed_join h.2 t.2⟩

/-- A fiber action has closed types. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem actionHasTy_closed (hsig : ClosedSig sig) :
    ∀ {env : TyEnv} {a : ActionTerm Op} {t : EffTy}, ActionHasTy sig env a t → ClosedEnv env →
      AnnotationsClosed .action a → t.Closed
  | _, _, _, .fork _ hp, henv, hs =>
    ⟨Bool.and_eq_true_iff.mpr (hasTy_closed hsig hp henv hs.2), rfl⟩
  | _, _, _, .forkIn _ hp _ _, henv, hs =>
    ⟨Bool.and_eq_true_iff.mpr (hasTy_closed hsig hp henv hs.2), rfl⟩
  | _, _, _, .forkScoped _ hp, henv, hs =>
    ⟨Bool.and_eq_true_iff.mpr (hasTy_closed hsig hp henv hs.2), rfl⟩
  | _, _, _, .runIn _ _ _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .interrupt _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .interruptScoped _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .interruptAll_self _ _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .interruptAll_by _ _ _ _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .awaitAll ht hl hf, henv, hs =>
    have hts := termTy_closed hsig henv hs.1 ht
    have hinner := closed_listOf hts hl
    ⟨Bool.and_eq_true_iff.mpr (closed_fiberTy hinner hf), rfl⟩
  | _, _, _, .awaitAllFailFast ht hl hf, henv, hs =>
    have hts := termTy_closed hsig henv hs.1 ht
    have hinner := closed_listOf hts hl
    ⟨Bool.and_eq_true_iff.mpr (closed_fiberTy hinner hf), rfl⟩
  | _, _, _, .snapshotChildren, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .awaitNewChildren _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .raceAll he, henv, hs => effsHasTy_closed hsig he henv hs.2
  | _, _, _, .setContext _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .getContext, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .getId, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .closeScope _ _ _ _, _, _ => ⟨rfl, rfl⟩
  | _, _, _, .getInterruptible, _, _ => ⟨rfl, rfl⟩

/-- A layer's error type is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem layerHasTy_closed (hsig : ClosedSig sig) :
    ∀ {l : LayerTerm Op} {t : LayerTy}, LayerHasTy sig l t → AnnotationsClosed .layer l →
      t.error.closed = true
  | _, _, .succeed _ _ _, _ => rfl
  | _, _, .effect hb _ _, hs => (hasTy_closed hsig hb ClosedEnv.nil hs.2).2
  | _, _, .effectDiscard hb, hs => (hasTy_closed hsig hb ClosedEnv.nil hs.2).2
  | _, _, .provide ha hb, hs =>
    UnionRule.closed_join (layerHasTy_closed hsig ha hs.2.1) (layerHasTy_closed hsig hb hs.2.2)
  | _, _, .provideMerge ha hb, hs =>
    UnionRule.closed_join (layerHasTy_closed hsig ha hs.2.1) (layerHasTy_closed hsig hb hs.2.2)
  | _, _, .merge ha hb, hs =>
    UnionRule.closed_join (layerHasTy_closed hsig ha hs.2.1) (layerHasTy_closed hsig hb hs.2.2)
  | _, _, .fresh hi, hs => layerHasTy_closed hsig hi hs.2
  | _, _, .orDie _, _ => rfl
  | _, _, .mergeAll hl, hs => layersHasTy_closed hsig hl hs.2

/-- A layer list's merged error type is closed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem layersHasTy_closed (hsig : ClosedSig sig) :
    ∀ {ls : LayerTerms Op} {t : LayerTy}, LayersHasTy sig ls t →
      AnnotationsClosed .layers ls → t.error.closed = true
  | _, _, .one hl, hs => layerHasTy_closed hsig hl hs.2.1
  | _, _, .cons hl hr, hs =>
    UnionRule.closed_join (layerHasTy_closed hsig hl hs.2.1) (layersHasTy_closed hsig hr hs.2.2)

end

end Judgments

/-! ## 6. The checker, and the native signature -/

/-- **A formed program that the checker admits has closed types**, at a closed environment and
a signature with closed atoms and closed service carriers (the claim `checked-types-closed`).
The annotations are formed outside a template, so each states a closed type
(`Formation.closed_of_formed`), and each rule of the checker keeps closed types closed
(`hasTy_closed`). The path is any path: the checker's answer does not depend on it. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem check_closed {Op : Type} [ScopedOp Op] (sig : Signature Op) (closed : ClosedSig sig)
    {env : TyEnv} (henv : ∀ t ∈ env, t.closed = true) {p : List Nat} {e : Eff Op} {t : EffTy}
    (formed : Formation.Formed (Formation.programSites e))
    (h : Checker.check sig env p e = .ok t) :
    t.answer.closed = true ∧ t.error.closed = true :=
  hasTy_closed closed (check_sound sig e env p t h) henv
    (Formation.annotationsClosed_of_formed formed)

/-- **A formed program that the whole-program checker admits has closed types.** The checker
types the program's expansion, and the expansion states what the program states
(`Formation.annotationsAll_expandRefs`). So the formation premise is the stored program's, with
its layer references as they are written. It is `check_closed` at the checker that admission
and the API run (`typeOfProgram`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem typeOfProgram_closed {Op : Type} [ScopedOp Op] (sig : Signature Op)
    (closed : ClosedSig sig) {e : Eff Op} {t : EffTy}
    (formed : Formation.Formed (Formation.programSites e))
    (h : typeOfProgram sig e = some t) :
    t.answer.closed = true ∧ t.error.closed = true := by
  unfold typeOfProgram at h
  split at h
  · have hann := Formation.annotationsAll_expandRefs _ e (Formation.annotationsClosed_of_formed formed)
    have hm := checkModule_sound sig _ t (Effect4.Laws.Auto.toOption_eq_some.mp h)
    generalize e.expandRefs = x at hann hm
    cases hm with
    -- a block's main program is checked at the block's signature, whose atoms and carriers are
    -- the signature's (decisions row 328)
    | @defs decls _ _ _ _ hmain =>
      exact hasTy_closed (sig := sig.withDefs decls) ⟨closed.atom, closed.service⟩ hmain
        ClosedEnv.nil hann.2.2
    | plain hd => exact hasTy_closed closed hd ClosedEnv.nil hann
  · exact nomatch h

/-- A native atom answers a closed type at closed arguments. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_nativeAtomTy {name : String} {tys : List Ty} {ty : Ty}
    (htys : ∀ t ∈ tys, t.closed = true) (h : nativeAtomTy name tys = some ty) :
    ty.closed = true := by
  obtain ⟨atom, _, hty⟩ := Option.bind_eq_some_iff.mp h
  exact atom.closed_typeOf htys hty

/-- A built-in service carrier is closed: read off the two tables. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_nativeServiceTy {key : ServiceKey} {ty : Ty}
    (h : nativeServiceTy key = some ty) : ty.closed = true := by
  unfold nativeServiceTy at h
  split at h
  · rename_i hfind
    cases h
    exact List.all_eq_true.mp
      (by decide : nativeReservedServiceTypes.all (fun entry => entry.2.closed) = true) _
      (List.mem_of_find?_eq_some hfind)
  · split at h
    · exact nomatch h
    · obtain ⟨entry, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
      exact List.all_eq_true.mp
        (by decide : nativeServiceTypes.all (fun entry => entry.2.closed) = true) entry
        (List.mem_of_find?_eq_some hfind)

/-- **The native signature has closed atoms and closed service carriers**, at every row table.
So `check_closed` asks nothing of a native program but its formed annotations. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closedSig_native (table : RowTable) : ClosedSig (nativeSignature table) :=
  ⟨fun _ _ _ h htys => closed_nativeAtomTy htys h, fun _ _ h => closed_nativeServiceTy h⟩

/-! ## 7. An application's signature: a declared carrier is a formation site

A declared service carrier is no template, so formation checks it strictly
(`Formation.serviceSites`). The signature's own admission (`admitSig`) keeps its local checks:
a carrier's formation is the formation pass's, as a row's is. So the premise on carriers
follows from the formed input, and program admission carries it. -/

namespace Formation

/-- Each declared carrier of a formed list of service sites is closed. A step of
`closedSig_app`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem services_closed {services : List (ServiceKey × Ty)}
    (h : Formed (serviceSites services)) : ∀ entry ∈ services, entry.2.closed = true := by
  intro entry hentry
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentry
  have hmem : (entry, i) ∈ services.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  exact closed_of_formed (path := ["service", toString i, "carrier"]) fun site hsite =>
    h site (List.mem_flatMap.mpr ⟨(entry, i), hmem, hsite⟩)

/-- The service sites of a formed input are formed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem inputFormed_services {Op : Type} [ScopedOp Op] {program : Eff Op} {table : List Row}
    {services : List (ServiceKey × Ty)} (h : InputFormed program table services) :
    Formed (serviceSites services) := fun site hsite =>
  h site (List.mem_append_right _ (List.mem_append_left _ hsite))

/-- The program sites of a formed input are formed. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem inputFormed_program {Op : Type} [ScopedOp Op] {program : Eff Op} {table : List Row}
    {services : List (ServiceKey × Ty)} (h : InputFormed program table services) :
    Formed (programSites program) := fun site hsite =>
  h site (List.mem_append_right _ (List.mem_append_right _ hsite))

end Formation

/-- A carrier that an application's signature answers is closed, when its declared carriers
are: the reserved carrier and the built-in ones are read off their tables. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closed_serviceTy {app : SigApp}
    (hservices : ∀ entry ∈ app.services, entry.2.closed = true) {key : ServiceKey} {ty : Ty}
    (h : app.serviceTy key = some ty) : ty.closed = true := by
  unfold SigApp.serviceTy at h
  split at h
  · rename_i hfind
    cases h
    exact List.all_eq_true.mp
      (by decide : nativeReservedServiceTypes.all (fun entry => entry.2.closed) = true) _
      (List.mem_of_find?_eq_some hfind)
  · split at h
    · exact nomatch h
    · split at h
      · rename_i hcode
        cases h
        obtain ⟨entry, hfind, rfl⟩ := Option.map_eq_some_iff.mp hcode
        exact hservices entry (List.mem_of_find?_eq_some hfind)
      · obtain ⟨entry, hfind, rfl⟩ := Option.map_eq_some_iff.mp h
        exact List.all_eq_true.mp
          (by decide : nativeServiceTypes.all (fun entry => entry.2.closed) = true) entry
          (List.mem_of_find?_eq_some hfind)

/-- **An application's signature has closed atoms and closed carriers when its declared
carriers are formed.** The atoms are the native ones. A step of `AdmittedProgram.closed`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem closedSig_app (app : SigApp) (h : Formation.Formed (Formation.serviceSites app.services)) :
    ClosedSig app.signature :=
  ⟨fun _ _ _ hatom htys => closed_nativeAtomTy htys hatom,
    fun _ _ hty => closed_serviceTy (Formation.services_closed h) hty⟩

/-- `typeOfProgram_closed` at an application's signature: formation of the input is its one
premise. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem typeOfProgram_closed_app (app : SigApp) {e : NativeEff} {t : EffTy}
    (formed : Formation.InputFormed e app.rows app.services)
    (h : typeOfProgram app.signature e = some t) :
    t.answer.closed = true ∧ t.error.closed = true :=
  typeOfProgram_closed _ (closedSig_app app (Formation.inputFormed_services formed))
    (Formation.inputFormed_program formed) h

/-- **An admitted program has closed types**, with no premise: its certificate holds the formed
input and the whole-program checker's answer. The claim `checked-types-closed` at program
admission. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem AdmittedProgram.closed {program : NativeEff} {app : SigApp}
    (admitted : AdmittedProgram program app) :
    admitted.ty.answer.closed = true ∧ admitted.ty.error.closed = true :=
  typeOfProgram_closed_app app admitted.formed admitted.typed

end Effect4.Program
