import Effect4.Program.Typed

namespace Effect4.Program
open Effect4 Effect4.Machine

theorem hasTy_ofMembers (v : Val) (xs : List Ty) (allocated : List String) :
    Val.hasTy v (Ty.ofMembers xs) allocated =
      xs.any (fun t => Val.hasTy v t allocated) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp only [Ty.ofMembers, List.any_cons, List.any_nil, Bool.or_false]
    | cons y ys =>
      change (Val.hasTy v x allocated || Val.hasTy v (Ty.ofMembers (y :: ys)) allocated) = _
      rw [ih]
      rfl

theorem hasTy_members (v : Val) (t : Ty) (allocated : List String) :
    t.members.any (fun t => Val.hasTy v t allocated) = Val.hasTy v t allocated := by
  induction t <;> try rfl
  all_goals try (simp only [Ty.members, List.any_cons, List.any_nil, Bool.or_false])
  case union a b iha ihb =>
    simp only [Ty.members, List.any_append, iha, ihb, Val.hasTy]

theorem any_row_normalize (xs : List Ty) (p : Ty → Bool) :
    (Effect4.Row.normalize xs).elems.any p = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mp ht, hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mpr ht, hp⟩

theorem causeAdmits_congr_at {f g : Val → Ty → Bool} (a b : Ty)
    (h : ∀ v, f v a = g v b) (c : CauseV) :
    causeAdmits f a c = causeAdmits g b c := by
  apply List.all_congr rfl
  intro r
  cases r with
  | fail e annotations =>
    cases e <;> try rfl
    all_goals exact h _
  | die d annotations => rfl
  | interrupt id annotations => rfl

/-- Every valid snapshot follows the same element rule as an ordinary list. -/
theorem hasTy_fibers (ids : List FiberId) (inner : Ty) (allocated : List String) :
    Val.hasTy (Val.fibers ids) (.list inner) allocated =
      ids.all (fun id => Val.hasTy (Val.fiber id) inner allocated) := by
  change (match Val.snapshot? (Val.fibers ids) with
    | some ids => ids.all (fun id => Val.hasTy (Val.fiber id) inner allocated)
    | none => false) = _
  rw [Val.snapshot?_fibers]

theorem hasTy_fibers_nil (inner : Ty) (allocated : List String) :
    Val.hasTy (Val.fibers []) (.list inner) allocated = true := by
  rw [hasTy_fibers]
  rfl

theorem hasTy_normalize (t : Ty) (v : Val) (allocated : List String) :
    Val.hasTy v t.normalize allocated = Val.hasTy v t allocated := by
  induction t generalizing v with
  | never | unit | nat | int | string | bool | handle | lit => rfl
  | except error value ihe ihv =>
    simp only [Ty.normalize, Val.hasTy]
    split <;> try rfl
    · exact ihe _
    · exact ihv _
  | fiberOf => rfl
  | option t ih =>
    simp only [Ty.normalize, Val.hasTy]
    split <;> try rfl
    exact ih _
  | prod a b iha ihb =>
    simp only [Ty.normalize, Val.hasTy]
    split <;> try rfl
    rw [iha, ihb]
  | list t ih =>
    simp only [Ty.normalize, Val.hasTy]
    split <;> try rfl
    · split <;> try rfl
      exact List.all_congr rfl (fun id => ih (Val.fiber id))
    · exact List.all_congr rfl ih
  | causeOf e ih =>
    simp only [Ty.normalize, Val.hasTy]
    split <;> try rfl
    exact causeAdmits_congr_at _ _ ih _
  | exitOf a e iha ihe =>
    simp only [Ty.normalize, Val.hasTy]
    split <;> try rfl
    · exact iha _
    · split <;> try rfl
      exact causeAdmits_congr_at _ _ ihe _
  | union a b iha ihb =>
    rw [Ty.normalize, hasTy_ofMembers, any_row_normalize, List.any_append,
      hasTy_members, hasTy_members, iha, ihb]
    rfl

theorem hasTy_of_normalize_eq {a b : Ty} (h : a.normalize = b.normalize)
    (v : Val) (allocated : List String) :
    Val.hasTy v a allocated = Val.hasTy v b allocated := by
  rw [← hasTy_normalize a, ← hasTy_normalize b, h]

end Effect4.Program

namespace Effect4.Program.Ty

theorem Normal.members_ascending {t : Ty} (h : Normal t) :
    Effect4.Ascending t.members := by
  cases h <;> try (simp [Ty.members, Effect4.Ascending])
  case row r children atoms =>
    rw [members_ofMembers r.elems atoms]
    exact r.ascending

theorem Normal.ofMembers_members {t : Ty} (h : Normal t) :
    ofMembers t.members = t := by
  cases h <;> try rfl
  case row r children atoms => rw [members_ofMembers r.elems atoms]

theorem join_eq_ofMembers (a b : Ty) :
    join a b = ofMembers (Effect4.Row.normalize
      ((normalize a).members ++ (normalize b).members)).elems := rfl

theorem normalize_join (a b : Ty) : normalize (join a b) = join a b :=
  normalize_idem (.union a b)

theorem members_join (a b : Ty) :
    members (join a b) = (Effect4.Row.normalize
      ((normalize a).members ++ (normalize b).members)).elems := by
  apply members_ofMembers
  intro t ht
  have ht := (Effect4.Row.mem_normalize t _).mp ht
  exact (List.mem_append.mp ht).elim members_isMember members_isMember

theorem join_comm (a b : Ty) : join a b = join b a := by
  rw [join_eq_ofMembers, join_eq_ofMembers]
  congr 1
  apply congrArg Effect4.Row.elems
  apply Effect4.Row.eq_of_mem_iff
  intro t
  simp only [Effect4.Row.mem_normalize, List.mem_append]
  exact or_comm

theorem join_assoc (a b c : Ty) : join (join a b) c = join a (join b c) := by
  rw [join_eq_ofMembers (join a b) c, join_eq_ofMembers a (join b c),
    normalize_join, normalize_join, members_join, members_join]
  congr 1
  apply congrArg Effect4.Row.elems
  apply Effect4.Row.eq_of_mem_iff
  intro t
  simp only [Effect4.Row.mem_normalize, List.mem_append]
  change (t ∈ Effect4.Row.normalize ((normalize a).members ++ (normalize b).members) ∨
      t ∈ (normalize c).members) ↔
    (t ∈ (normalize a).members ∨
      t ∈ Effect4.Row.normalize ((normalize b).members ++ (normalize c).members))
  simp only [Effect4.Row.mem_normalize, List.mem_append]
  exact or_assoc

theorem join_self (t : Ty) : join t t = normalize t := by
  rw [join_eq_ofMembers]
  have h := normal_normalize t
  have hr : Effect4.Row.normalize ((normalize t).members ++ (normalize t).members) =
      Effect4.Row.mk (normalize t).members h.members_ascending := by
    apply Effect4.Row.eq_of_mem_iff
    intro x
    change x ∈ Effect4.Row.normalize ((normalize t).members ++ (normalize t).members) ↔
      x ∈ (normalize t).members
    rw [Effect4.Row.mem_normalize]
    simp only [List.mem_append, or_self]
  rw [hr]
  exact h.ofMembers_members

theorem join_never (t : Ty) : join .never t = normalize t := by
  rw [join_eq_ofMembers]
  change ofMembers (Effect4.Row.normalize ([] ++ (normalize t).members)).elems = _
  rw [List.nil_append, Effect4.Row.normalize_of_ascending _ (normal_normalize t).members_ascending]
  exact (normal_normalize t).ofMembers_members

theorem join_never_right (t : Ty) : join t .never = normalize t := by
  rw [join_comm, join_never]

end Effect4.Program.Ty

namespace Effect4.Program.CTy

@[simp] theorem join_self (t : CTy) : join t t = t := by
  apply Subtype.ext
  change Ty.join t.val t.val = t.val
  rw [Ty.join_self]
  exact t.property

@[simp] theorem join_never (t : CTy) : join never t = t := by
  apply Subtype.ext
  change Ty.join .never t.val = t.val
  rw [Ty.join_never]
  exact t.property

@[simp] theorem join_never_right (t : CTy) : join t never = t := by
  apply Subtype.ext
  change Ty.join t.val .never = t.val
  rw [Ty.join_never_right]
  exact t.property

theorem join_comm (a b : CTy) : join a b = join b a := by
  apply Subtype.ext
  exact Ty.join_comm a.val b.val

theorem join_assoc (a b c : CTy) : join (join a b) c = join a (join b c) := by
  apply Subtype.ext
  exact Ty.join_assoc a.val b.val c.val

end Effect4.Program.CTy
