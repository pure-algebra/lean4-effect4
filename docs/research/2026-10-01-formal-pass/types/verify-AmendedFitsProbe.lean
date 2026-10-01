import Effect4.Laws.Program.Typed.Membership
import Effect4.Laws.Program.TypeAlgebra

/-!
# Verifier of seat TYPES (formal pass, 2026-10-01): TY-01's amendment, proved on a copy of `Fits`

Research probe, outside every root; nothing imports it.

The seat's TY-01 amendment: compare handle declarations in the checker's order
`subN a b := sub (normalize a) (normalize b)` inside `Fits`'s fiber, cell and deferred arms, then
prove `fits_normalize`, `fits_subN`, `fits_join_left/right` "as `hasTy_normalize` is proved". The
seat proved only the handle-arm lemmas (probe A §6); the central lemma was reading.

This probe states the amended judgment `FitsN` as a copy of the tree's `Fits`
(`Laws/Program/Typed/Membership.lean:87-148`) with those three arms changed, reusing the tree's
`HandleFits`, `ServicesFit`, `Live` and `CauseFits` unchanged (their query types are fixed, so
normalization does not reach them), and proves:

* `fitsN_live`, `fitsN_sub` (raw `sub`, the copy of `fits_sub` with `subN_trans`);
* `fitsN_normalize` (**the amendment's central lemma**): `FitsN w v t.normalize ↔ FitsN w v t`;
* `fitsN_subN`, `fitsN_join_left`, `fitsN_join_right`;
* the seat's M5 leaf under the amendment, and the same leaf refuted for the tree's `Fits` (red).
-/

set_option autoImplicit false

namespace Research.TypesVerify.Amended

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Machine.Env (Requirement)

/-! ## The checker's order and the amended arms -/

def subN (a b : Ty) : Bool := Ty.sub a.normalize b.normalize

theorem subN_trans {a b c : Ty} (hab : subN a b = true) (hbc : subN b c = true) :
    subN a c = true :=
  Ty.sub_trans _ _ _ hab hbc

theorem sub_le_subN {a b : Ty} (h : Ty.sub a b = true) : subN a b = true :=
  Ty.sub_normalize_of_sub a b h

theorem subN_normalize_right (x a : Ty) : subN x a.normalize = subN x a := by
  unfold subN
  rw [Ty.normalize_idem]

theorem subN_normalize_left (a x : Ty) : subN a.normalize x = subN a x := by
  unfold subN
  rw [Ty.normalize_idem]

def EquivN (declared t : Ty) : Prop := subN declared t = true ∧ subN t declared = true

def RefDeclaredN (w : Typed.World) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ EquivN t' t

def PromiseDeclaredN (w : Typed.World) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ EquivN a' a ∧ EquivN e' e

def FiberDeclaredN (w : Typed.World) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ subN fty.answer a = true ∧ subN fty.error e = true

/-- The tree's `Fits`, copied, with the three declaration arms in the checker's order. -/
def FitsN (w : Typed.World) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w kind index target
    | _ => target = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .option a =>
    match v with
    | .none => True
    | .some x => FitsN w x a
    | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, FitsN w (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, FitsN w x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => FitsN w x a ∧ FitsN w y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => FitsN w err e
    | .ctor 1 [val] => FitsN w val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => FitsN w x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => FitsN w x e) c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => FitsN w x e) c
    | none => False
  | .fiberOf a e =>
    match v with
    | Value.fiber index => FiberDeclaredN w ⟨index⟩ a e
    | _ => False
  | .union l r => FitsN w v l ∨ FitsN w v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t =>
    match v with
    | Value.cell index => RefDeclaredN w ⟨index⟩ t
    | _ => False
  | .deferredOf a e =>
    match v with
    | Value.promise index => PromiseDeclaredN w ⟨index⟩ a e
    | _ => False
  | .var _ => False
  | .unknown => Live w v

/-! ## Liveness (the copy of `fits_live`) -/

theorem liveN_fiber {w : Typed.World} {index : Nat} {a e : Ty} (h : FiberDeclaredN w ⟨index⟩ a e) :
    Live w (Value.fiber index) := by
  obtain ⟨fty, hΓ, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.fiber ⟨index⟩).keys := hk
  rw [Val.keys_fiber, List.mem_singleton] at hk'
  subst hk'
  show (w.Γ ⟨index⟩).isSome = true
  rw [hΓ]
  rfl

theorem liveN_cell {w : Typed.World} {index : Nat} {t : Ty} (h : RefDeclaredN w ⟨index⟩ t) :
    Live w (Value.cell index) := by
  obtain ⟨t', hΡ, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.cell ⟨index⟩).keys := hk
  rw [Val.keys_cell, List.mem_singleton] at hk'
  subst hk'
  show (w.Ρ ⟨index⟩).isSome = true
  rw [hΡ]
  rfl

theorem liveN_promise {w : Typed.World} {index : Nat} {a e : Ty}
    (h : PromiseDeclaredN w ⟨index⟩ a e) : Live w (Value.promise index) := by
  obtain ⟨a', e', hPi, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.promise ⟨index⟩).keys := hk
  rw [Val.keys_promise, List.mem_singleton] at hk'
  subst hk'
  show (w.«Π» ⟨index⟩).isSome = true
  rw [hPi]
  rfl

theorem fitsN_live (w : Typed.World) : ∀ (ty : Ty) (v : Val), FitsN w v ty → Live w v := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | nat =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | int => intro v h; exact h.elim
  | string =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | bool =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | handle target =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_handle h
    · obtain ⟨_, _, _, _, hl⟩ := h
      exact hl
  | option a ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_of_keys_nil rfl
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        rw [Val.snapshot?_exact hids]
        intro k hk
        rw [Val.keys_fibers, List.mem_map] at hk
        obtain ⟨id, hid, rfl⟩ := hk
        exact ih _ (h id hid) (Handle.fiber id) (by rw [Val.keys_fiber]; exact List.mem_singleton_self _)
      · exact h.elim
    · exact live_list fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [FitsN] at h
    split at h
    · rename_i x y
      refine live_list fun z hz => ?_
      rw [List.mem_cons, List.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact iha _ h.1
      · exact ihb _ h.2
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_ctor_one (ihe _ h)
    · exact live_ctor_one (iha _ h)
    · exact h.elim
  | exitOf a e iha _ =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_ctor_one (iha _ h)
    · rename_i written
      split at h
      · rename_i c hc
        refine live_ctor_one (live_of_keys_nil ?_)
        rw [Store.Image.ofVal_exact causeImage hc]
        exact Val.keys_causeImage c
      · exact h.elim
    · exact h.elim
  | causeOf e _ =>
    intro v h
    simp only [FitsN] at h
    split at h
    · rename_i c hc
      exact live_of_keys_nil (keys_of_cause hc)
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact liveN_fiber h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    simp only [FitsN] at h
    exact h.elim (ihl v) (ihr v)
  | lit s =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | refOf t _ =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact liveN_cell h
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [FitsN] at h
    split at h
    · exact liveN_promise h
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact h

/-! ## Closure under the raw order (the copy of `fits_sub`) -/

theorem fitsN_sub (w : Typed.World) {a b : Ty} (hsub : Ty.sub a b = true) :
    ∀ v, FitsN w v a → FitsN w v b := by
  fun_induction Ty.sub a b
  case case1 => intro v h; exact h
  case case2 => intro v h; exact h.elim
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    exact h.elim (iha h1 v) (ihb h2 v)
  case case4 a b1 b2 _ _ _ iha ihb =>
    intro v h
    exact (Bool.or_eq_true_iff.mp hsub).elim (fun hx => Or.inl (iha hx v h))
      (fun hx => Or.inr (ihb hx v h))
  case case5 => intro v h; exact fitsN_live w _ v h
  case case6 =>
    intro v h
    simp only [FitsN] at h
    split at h
    · trivial
    · exact h.elim
  case case7 x y _ ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · trivial
    · rename_i z
      exact ih hsub z h
    · exact h.elim
  case case8 x y _ ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [FitsN, hids]
        exact fun id hid => ih hsub _ (h id hid)
      · exact h.elim
    · exact fun z hz => ih hsub z (h z hz)
    · exact h.elim
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · exact ⟨iha h1 _ h.1, ihb h2 _ h.2⟩
    · exact h.elim
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · exact ihe h1 _ h
    · exact iha h2 _ h
    · exact h.elim
  case case11 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · exact iha h1 _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [FitsN, hc]
        exact causeFits_map (fun x hx => ihe h2 x hx) h
      · exact h.elim
    · exact h.elim
  case case12 e1 e2 _ ih =>
    intro v h
    simp only [FitsN] at h
    split at h
    · rename_i c hc
      simp only [FitsN, hc]
      exact causeFits_map (fun x hx => ih hsub x hx) h
    · exact h.elim
  case case13 a1 e1 a2 e2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · obtain ⟨fty, hs, ha, he⟩ := h
      exact ⟨fty, hs, subN_trans ha (sub_le_subN h1), subN_trans he (sub_le_subN h2)⟩
    · exact h.elim
  case case14 a1 a2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [FitsN] at h
    split at h
    · obtain ⟨t', hs, hl, hr⟩ := h
      exact ⟨t', hs, subN_trans hl (sub_le_subN h1), subN_trans (sub_le_subN h2) hr⟩
    · exact h.elim
  case case15 a1 e1 a2 e2 _ _ _ _ _ =>
    obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    intro v h
    simp only [FitsN] at h
    split at h
    · obtain ⟨a', e', hs, ⟨ha1, ha2⟩, ⟨he1, he2⟩⟩ := h
      exact ⟨a', e', hs, ⟨subN_trans ha1 (sub_le_subN h1), subN_trans (sub_le_subN h2) ha2⟩,
        ⟨subN_trans he1 (sub_le_subN h3), subN_trans (sub_le_subN h4) he2⟩⟩
    · exact h.elim
  case case16 => exact Bool.noConfusion hsub

/-! ## Membership through the finite-row algebra (the `Prop` twins of `hasTy_*`) -/

theorem exists_singleton_iff (P : Ty → Prop) (t : Ty) : (∃ x ∈ [t], P x) ↔ P t :=
  ⟨fun ⟨x, hx, hp⟩ => by rw [List.mem_singleton] at hx; subst hx; exact hp,
    fun hp => ⟨t, List.mem_singleton_self t, hp⟩⟩

theorem fitsN_ofMembers (w : Typed.World) (v : Val) :
    ∀ xs : List Ty, FitsN w v (Ty.ofMembers xs) ↔ ∃ t ∈ xs, FitsN w v t
  | [] => ⟨fun h => h.elim, fun ⟨_, hx, _⟩ => nomatch hx⟩
  | [x] => (exists_singleton_iff (FitsN w v) x).symm
  | x :: y :: ys => by
    have ih := fitsN_ofMembers w v (y :: ys)
    show (FitsN w v x ∨ FitsN w v (Ty.ofMembers (y :: ys))) ↔ _
    rw [ih]
    constructor
    · rintro (h | ⟨t, ht, hv⟩)
      · exact ⟨x, List.mem_cons_self .., h⟩
      · exact ⟨t, List.mem_cons_of_mem x ht, hv⟩
    · rintro ⟨t, ht, hv⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl hv
      · exact Or.inr ⟨t, ht, hv⟩

theorem fitsN_members (w : Typed.World) (v : Val) (t : Ty) :
    (∃ x ∈ t.members, FitsN w v x) ↔ FitsN w v t := by
  induction t with
  | never => exact ⟨fun ⟨_, hx, _⟩ => (nomatch hx), fun h => h.elim⟩
  | union a b iha ihb =>
    show (∃ x ∈ a.members ++ b.members, FitsN w v x) ↔ (FitsN w v a ∨ FitsN w v b)
    rw [← iha, ← ihb]
    constructor
    · rintro ⟨x, hx, hv⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, hv⟩
      · exact Or.inr ⟨x, hx, hv⟩
    · rintro (⟨x, hx, hv⟩ | ⟨x, hx, hv⟩)
      · exact ⟨x, List.mem_append_left _ hx, hv⟩
      · exact ⟨x, List.mem_append_right _ hx, hv⟩
  | unknown => exact exists_singleton_iff _ _
  | unit => exact exists_singleton_iff _ _
  | nat => exact exists_singleton_iff _ _
  | int => exact exists_singleton_iff _ _
  | string => exact exists_singleton_iff _ _
  | bool => exact exists_singleton_iff _ _
  | handle _ => exact exists_singleton_iff _ _
  | option _ _ => exact exists_singleton_iff _ _
  | list _ _ => exact exists_singleton_iff _ _
  | prod _ _ _ _ => exact exists_singleton_iff _ _
  | except _ _ _ _ => exact exists_singleton_iff _ _
  | exitOf _ _ _ _ => exact exists_singleton_iff _ _
  | causeOf _ _ => exact exists_singleton_iff _ _
  | fiberOf _ _ _ _ => exact exists_singleton_iff _ _
  | lit _ => exact exists_singleton_iff _ _
  | refOf _ _ => exact exists_singleton_iff _ _
  | deferredOf _ _ _ _ => exact exists_singleton_iff _ _
  | var _ => exact exists_singleton_iff _ _

theorem fitsN_factors (w : Typed.World) (v : Val) (t : Ty) :
    (∃ x ∈ t.factors, FitsN w v x) ↔ FitsN w v t := by
  cases t with
  | never => exact exists_singleton_iff _ _
  | _ => exact fitsN_members w v _

theorem fitsN_normalizeRow (w : Typed.World) (v : Val) (xs : List Ty) :
    (∃ t ∈ (Ty.normalizeRow xs).elems, FitsN w v t) ↔ ∃ t ∈ xs, FitsN w v t := by
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, ((Ty.mem_normalizeRow t xs).mp ht).1, hv⟩
  · rintro ⟨t, ht, hv⟩
    have ht' : t ∈ (Effect4.Row.normalize xs).elems := (Effect4.Row.mem_normalize t xs).mpr ht
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage Ty.sub Ty.sub_refl Ty.sub_trans
      (Effect4.Row.normalize xs).elems t ht'
    exact ⟨u, hu, fitsN_sub w htu v hv⟩

theorem fitsN_prod_iff (w : Typed.World) (v : Val) (a b : Ty) :
    FitsN w v (.prod a b) ↔ ∃ p q, v = .list [p, q] ∧ FitsN w p a ∧ FitsN w q b := by
  simp only [FitsN]
  split
  · rename_i p q
    exact ⟨fun h => ⟨p, q, rfl, h.1, h.2⟩, fun ⟨p', q', he, h1, h2⟩ => by cases he; exact ⟨h1, h2⟩⟩
  · rename_i hne
    exact ⟨fun h => h.elim, fun ⟨p', q', he, _, _⟩ => absurd he (hne p' q')⟩

theorem fitsN_productMembers (w : Typed.World) (v : Val) (a b : Ty) :
    (∃ x ∈ Ty.productMembers a b, FitsN w v x) ↔ FitsN w v (.prod a b) := by
  rw [fitsN_prod_iff]
  constructor
  · rintro ⟨z, hz, hv⟩
    obtain ⟨x, hx, hz2⟩ := List.mem_flatMap.mp hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz2
    obtain ⟨p, q, rfl, hp, hq⟩ := (fitsN_prod_iff w v x y).mp hv
    exact ⟨p, q, rfl, (fitsN_factors w p a).mp ⟨x, hx, hp⟩, (fitsN_factors w q b).mp ⟨y, hy, hq⟩⟩
  · rintro ⟨p, q, rfl, hp, hq⟩
    obtain ⟨x, hx, hpx⟩ := (fitsN_factors w p a).mpr hp
    obtain ⟨y, hy, hqy⟩ := (fitsN_factors w q b).mpr hq
    exact ⟨.prod x y, List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩,
      (fitsN_prod_iff w _ x y).mpr ⟨p, q, rfl, hpx, hqy⟩⟩

theorem causeFits_iff {m1 m2 : Val → Prop} (h : ∀ x, m1 x ↔ m2 x) (c : CauseV) :
    CauseFits m1 c ↔ CauseFits m2 c :=
  ⟨causeFits_map (fun x hx => (h x).mp hx), causeFits_map (fun x hx => (h x).mpr hx)⟩

/-! ## The handle arms (the seat's probe A §6, re-proved here) -/

theorem fiberDeclaredN_normalize (w : Typed.World) (id : FiberId) (a e : Ty) :
    FiberDeclaredN w id a.normalize e.normalize ↔ FiberDeclaredN w id a e := by
  unfold FiberDeclaredN
  simp only [subN_normalize_right]

theorem equivN_normalize (declared t : Ty) : EquivN declared t.normalize ↔ EquivN declared t := by
  unfold EquivN
  rw [subN_normalize_right, subN_normalize_left]

/-! ## The central lemma -/

/-- **TY-01's central lemma, proved for the amended judgment.** -/
theorem fitsN_normalize (w : Typed.World) : ∀ (t : Ty) (v : Val), FitsN w v t.normalize ↔ FitsN w v t := by
  intro t
  induction t with
  | never => intro v; exact Iff.rfl
  | unknown => intro v; exact Iff.rfl
  | unit => intro v; exact Iff.rfl
  | nat => intro v; exact Iff.rfl
  | int => intro v; exact Iff.rfl
  | string => intro v; exact Iff.rfl
  | bool => intro v; exact Iff.rfl
  | handle _ => intro v; exact Iff.rfl
  | lit _ => intro v; exact Iff.rfl
  | var _ => intro v; exact Iff.rfl
  | union a b iha ihb =>
    intro v
    show FitsN w v (Ty.ofMembers (Ty.normalizeRow (a.normalize.members ++ b.normalize.members)).elems) ↔
      (FitsN w v a ∨ FitsN w v b)
    rw [fitsN_ofMembers, fitsN_normalizeRow, ← iha, ← ihb, ← fitsN_members w v a.normalize,
      ← fitsN_members w v b.normalize]
    constructor
    · rintro ⟨x, hx, hv⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, hv⟩
      · exact Or.inr ⟨x, hx, hv⟩
    · rintro (⟨x, hx, hv⟩ | ⟨x, hx, hv⟩)
      · exact ⟨x, List.mem_append_left _ hx, hv⟩
      · exact ⟨x, List.mem_append_right _ hx, hv⟩
  | prod a b iha ihb =>
    intro v
    show FitsN w v (Ty.ofMembers (Ty.normalizeRow (Ty.productMembers a.normalize b.normalize)).elems) ↔
      FitsN w v (.prod a b)
    rw [fitsN_ofMembers, fitsN_normalizeRow, fitsN_productMembers, fitsN_prod_iff, fitsN_prod_iff]
    constructor
    · rintro ⟨p, q, hv, hp, hq⟩
      exact ⟨p, q, hv, (iha p).mp hp, (ihb q).mp hq⟩
    · rintro ⟨p, q, hv, hp, hq⟩
      exact ⟨p, q, hv, (iha p).mpr hp, (ihb q).mpr hq⟩
  | option t ih =>
    intro v
    show FitsN w v (.option t.normalize) ↔ FitsN w v (.option t)
    simp only [FitsN]
    split
    · exact Iff.rfl
    · exact ih _
    · exact Iff.rfl
  | list t ih =>
    intro v
    show FitsN w v (.list t.normalize) ↔ FitsN w v (.list t)
    simp only [FitsN]
    split
    · split
      · exact forall₂_congr fun id _ => ih (Val.fiber id)
      · exact Iff.rfl
    · exact forall₂_congr fun x _ => ih x
    · exact Iff.rfl
  | except e a ihe iha =>
    intro v
    show FitsN w v (.except e.normalize a.normalize) ↔ FitsN w v (.except e a)
    simp only [FitsN]
    split
    · exact ihe _
    · exact iha _
    · exact Iff.rfl
  | exitOf a e iha ihe =>
    intro v
    show FitsN w v (.exitOf a.normalize e.normalize) ↔ FitsN w v (.exitOf a e)
    simp only [FitsN]
    split
    · exact iha _
    · split
      · exact causeFits_iff (fun x => ihe x) _
      · exact Iff.rfl
    · exact Iff.rfl
  | causeOf e ih =>
    intro v
    show FitsN w v (.causeOf e.normalize) ↔ FitsN w v (.causeOf e)
    simp only [FitsN]
    split
    · exact causeFits_iff (fun x => ih x) _
    · exact Iff.rfl
  | fiberOf a e _ _ =>
    intro v
    show FitsN w v (.fiberOf a.normalize e.normalize) ↔ FitsN w v (.fiberOf a e)
    simp only [FitsN]
    split
    · exact fiberDeclaredN_normalize w _ a e
    · exact Iff.rfl
  | refOf t _ =>
    intro v
    show FitsN w v (.refOf t.normalize) ↔ FitsN w v (.refOf t)
    simp only [FitsN]
    split
    · unfold RefDeclaredN
      exact exists_congr fun t' => and_congr_right fun _ => equivN_normalize t' t
    · exact Iff.rfl
  | deferredOf a e _ _ =>
    intro v
    show FitsN w v (.deferredOf a.normalize e.normalize) ↔ FitsN w v (.deferredOf a e)
    simp only [FitsN]
    split
    · unfold PromiseDeclaredN
      exact exists_congr fun a' => exists_congr fun e' => and_congr_right fun _ =>
        and_congr (equivN_normalize a' a) (equivN_normalize e' e)
    · exact Iff.rfl

/-! ## The closures the M5–M7 proofs need -/

theorem fitsN_subN (w : Typed.World) {a b : Ty} (h : subN a b = true) (v : Val)
    (hv : FitsN w v a) : FitsN w v b :=
  (fitsN_normalize w b v).mp (fitsN_sub w h v ((fitsN_normalize w a v).mpr hv))

theorem fitsN_join_left (w : Typed.World) (a b : Ty) (v : Val) (h : FitsN w v a) :
    FitsN w v (Ty.join a b) :=
  (fitsN_normalize w (.union a b) v).mpr (Or.inl h)

theorem fitsN_join_right (w : Typed.World) (a b : Ty) (v : Val) (h : FitsN w v b) :
    FitsN w v (Ty.join a b) :=
  (fitsN_normalize w (.union a b) v).mpr (Or.inr h)

/-! ## The seat's M5 leaf, both ways -/

abbrev u : Ty := Ty.normalize (.union .nat .string)
abbrev T : Ty := .prod u .unit

theorem T_not_sub : Ty.sub T T.normalize = false := by decide +kernel

/-- **Red control (proved).** The tree's `Fits`: a fiber declared at `T` does not fit the join of
`fiberOf T never` with itself (what a `select` returning the handle twice types at). -/
theorem tree_join_fails (w : Typed.World) (id : FiberId)
    (hΓ : w.Γ id = some ⟨T, .never, Requirement.empty⟩) :
    ¬ Fits w (Val.fiber id) (Ty.join (.fiberOf T .never) (.fiberOf T .never)) := by
  rw [Ty.join_self]
  intro h
  change FiberDeclared w id T.normalize .never at h
  obtain ⟨fty, hΓ', ha, _⟩ := h
  rw [hΓ] at hΓ'
  cases hΓ'
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub] at ha'
  exact Bool.noConfusion ha'

/-- **The same leaf under the amendment (proved)**, through the general join closure. -/
theorem amended_join_holds (w : Typed.World) (id : FiberId)
    (hΓ : w.Γ id = some ⟨T, .never, Requirement.empty⟩) :
    FitsN w (Val.fiber id) (Ty.join (.fiberOf T .never) (.fiberOf T .never)) :=
  fitsN_join_left w _ _ _ ⟨⟨T, .never, Requirement.empty⟩, hΓ, Ty.sub_refl _, Ty.sub_refl _⟩

end Research.TypesVerify.Amended

#print axioms Research.TypesVerify.Amended.fitsN_live
#print axioms Research.TypesVerify.Amended.fitsN_sub
#print axioms Research.TypesVerify.Amended.fitsN_normalizeRow
#print axioms Research.TypesVerify.Amended.fitsN_productMembers
#print axioms Research.TypesVerify.Amended.fitsN_normalize
#print axioms Research.TypesVerify.Amended.fitsN_subN
#print axioms Research.TypesVerify.Amended.fitsN_join_left
#print axioms Research.TypesVerify.Amended.fitsN_join_right
#print axioms Research.TypesVerify.Amended.tree_join_fails
#print axioms Research.TypesVerify.Amended.amended_join_holds
