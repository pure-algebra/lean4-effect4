import Effect4.Program.Typed

namespace Effect4.Program.Ty

private theorem sub_never_core (t : Ty) : sub .never t = true := by
  unfold sub
  split <;> rfl

/-- Absorption's finite maximal-member witness needs transitivity. The public order
theorems are exposed by the subsequent canonical-order slice. -/
private theorem sub_trans_core (a b c : Ty) (hab : sub a b = true) (hbc : sub b c = true) :
    sub a c = true := by
  by_cases hac : a = c
  · subst c; exact sub_refl a
  by_cases habEq : a = b
  · subst b; exact hbc
  by_cases hbcEq : b = c
  · subst c; exact hab
  by_cases ha : isMember a = true
  · by_cases hb : isMember b = true
    · by_cases hc : isMember c = true
      · cases a <;> cases b <;> simp only [isMember] at ha hb <;> try contradiction
        all_goals
          unfold sub at hab
          simp only [habEq, ↓reduceIte, Bool.and_eq_true, Bool.false_eq_true] at hab
        all_goals
          cases c <;> simp only [isMember] at hc <;> try contradiction
          all_goals
            unfold sub at hbc ⊢
            simp only [hbcEq, hac, ↓reduceIte, Bool.and_eq_true, Bool.false_eq_true] at hbc ⊢
          all_goals
            first
            | exact sub_trans_core _ _ _ hab hbc
            | exact ⟨sub_trans_core _ _ _ hab.1 hbc.1, sub_trans_core _ _ _ hab.2 hbc.2⟩
      · cases c <;> simp only [isMember] at hc <;> try contradiction
        case never =>
          cases b <;> simp only [isMember] at hb <;> try contradiction
          all_goals
            unfold sub at hbc
            simp only [hbcEq, ↓reduceIte, Bool.false_eq_true] at hbc
        case union c1 c2 =>
          rw [sub_union_right _ _ _ hb] at hbc
          rw [sub_union_right _ _ _ ha]
          rcases Bool.or_eq_true_iff.mp hbc with h | h
          · exact Bool.or_eq_true_iff.mpr (Or.inl (sub_trans_core a b c1 hab h))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (sub_trans_core a b c2 hab h))
    · cases b <;> simp only [isMember] at hb <;> try contradiction
      case never =>
        cases a <;> simp only [isMember] at ha <;> try contradiction
        all_goals
          unfold sub at hab
          simp only [habEq, ↓reduceIte, Bool.false_eq_true] at hab
      case union b1 b2 =>
        rw [sub_union_right _ _ _ ha] at hab
        rw [sub_union_left _ _ _ hbcEq] at hbc
        rcases Bool.and_eq_true_iff.mp hbc with ⟨h1, h2⟩
        rcases Bool.or_eq_true_iff.mp hab with h | h
        · exact sub_trans_core a b1 c h h1
        · exact sub_trans_core a b2 c h h2
  · cases a <;> simp only [isMember] at ha <;> try contradiction
    case never => exact sub_never_core c
    case union a1 a2 =>
      rw [sub_union_left _ _ _ habEq] at hab
      rw [sub_union_left _ _ _ hac]
      rcases Bool.and_eq_true_iff.mp hab with ⟨h1, h2⟩
      exact Bool.and_eq_true_iff.mpr ⟨sub_trans_core a1 b c h1 hbc, sub_trans_core a2 b c h2 hbc⟩
termination_by sizeOf a + sizeOf b + sizeOf c

end Effect4.Program.Ty

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
    simp only [List.any_append, iha, ihb, Val.hasTy]

theorem any_row_normalize (xs : List Ty) (p : Ty → Bool) :
    (Effect4.Row.normalize xs).elems.any p = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mp ht, hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mpr ht, hp⟩

theorem hasTy_normalizeRow (v : Val) (xs : List Ty) (allocated : List String) :
    (Ty.normalizeRow xs).elems.any (fun t => Val.hasTy v t allocated) =
      xs.any (fun t => Val.hasTy v t allocated) := by
  rw [← any_row_normalize xs (fun t => Val.hasTy v t allocated)]
  apply Bool.eq_iff_iff.mpr
  simp only [Ty.normalizeRow, List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, Effect4.Row.antichain_subset Ty.sub ht, hv⟩
  · rintro ⟨t, ht, hv⟩
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage Ty.sub Ty.sub_refl
      Ty.sub_trans_core (Effect4.Row.normalize xs).elems t ht
    exact ⟨u, hu, hasTy_sub t u v allocated htu hv⟩

theorem hasTy_factors (v : Val) (t : Ty) (allocated : List String) :
    t.factors.any (fun t => Val.hasTy v t allocated) = Val.hasTy v t allocated := by
  cases t with
  | never => rfl
  | _ => exact hasTy_members v _ allocated

theorem hasTy_productMembers (v : Val) (a b : Ty) (allocated : List String) :
    (Ty.productMembers a b).any (fun t => Val.hasTy v t allocated) =
      Val.hasTy v (.prod a b) allocated := by
  simp only [Ty.productMembers, List.any_flatMap, List.any_map, Function.comp_def]
  simp only [Val.hasTy]
  split
  · rename_i x y
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨ta, hta, tb, htb, hx, hy⟩
      exact ⟨(Bool.eq_iff_iff.mp (hasTy_factors x a allocated)).mp
        (List.any_eq_true.mpr ⟨ta, hta, hx⟩),
        (Bool.eq_iff_iff.mp (hasTy_factors y b allocated)).mp
        (List.any_eq_true.mpr ⟨tb, htb, hy⟩)⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨ta, hta, hx⟩ := List.any_eq_true.mp
        ((Bool.eq_iff_iff.mp (hasTy_factors x a allocated)).mpr hx)
      obtain ⟨tb, htb, hy⟩ := List.any_eq_true.mp
        ((Bool.eq_iff_iff.mp (hasTy_factors y b allocated)).mpr hy)
      exact ⟨ta, hta, tb, htb, hx, hy⟩
  · simp

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
    rw [Ty.normalize, hasTy_ofMembers, hasTy_normalizeRow, hasTy_productMembers]
    simp only [Val.hasTy]
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
    rw [Ty.normalize, hasTy_ofMembers, hasTy_normalizeRow, List.any_append,
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
  case row r children atoms maximal =>
    rw [members_ofMembers r.elems atoms]
    exact r.ascending

theorem Normal.ofMembers_members {t : Ty} (h : Normal t) :
    ofMembers t.members = t := by
  cases h <;> try rfl
  case row r children atoms maximal => rw [members_ofMembers r.elems atoms]

theorem Normal.members_maximal {t : Ty} (h : Normal t) :
    ∀ x ∈ t.members, ∀ y ∈ t.members, sub x y = true → sub y x = true := by
  intro x hx y hy hxy
  cases h <;> try (simp only [Ty.members, List.mem_singleton] at hx hy; subst x; subst y; exact hxy)
  case never => exact False.elim (List.not_mem_nil hx)
  case row r children atoms maximal =>
    rw [members_ofMembers r.elems atoms] at hx hy
    exact maximal x hx y hy hxy

theorem normalizeRow_congr {xs ys : List Ty} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    normalizeRow xs = normalizeRow ys := by
  apply Effect4.Row.eq_of_mem_iff
  intro x
  change x ∈ (normalizeRow xs).elems ↔ x ∈ (normalizeRow ys).elems
  simp only [mem_normalizeRow, h]

theorem normalizeRow_append_comm (xs ys : List Ty) :
    normalizeRow (xs ++ ys) = normalizeRow (ys ++ xs) := by
  apply normalizeRow_congr
  intro x
  simp only [List.mem_append, or_comm]

theorem normalizeRow_coverage (xs : List Ty) (x : Ty) (hx : x ∈ xs) :
    ∃ y ∈ (normalizeRow xs).elems, sub x y = true :=
  Effect4.Row.antichain_coverage sub sub_refl sub_trans_core
    (Effect4.Row.normalize xs).elems x ((Effect4.Row.mem_normalize x xs).mpr hx)

theorem normalizeRow_append_left (xs ys : List Ty) :
    normalizeRow ((normalizeRow xs).elems ++ ys) = normalizeRow (xs ++ ys) := by
  apply Effect4.Row.eq_of_mem_iff
  intro x
  change x ∈ (normalizeRow ((normalizeRow xs).elems ++ ys)).elems ↔
    x ∈ (normalizeRow (xs ++ ys)).elems
  rw [mem_normalizeRow, mem_normalizeRow]
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ ((mem_normalizeRow x xs).mp hx).1
      · exact List.mem_append_right _ hx
    · intro y hy hxy
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨z, hz, hyz⟩ := normalizeRow_coverage xs y hy
        have hzx := hm z (List.mem_append_left _ hz) (sub_trans_core x y z hxy hyz)
        exact sub_trans_core y z x hyz hzx
      · exact hm y (List.mem_append_right _ hy) hxy
  · rintro ⟨hx, hm⟩
    refine ⟨?_, ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · apply List.mem_append_left
        exact (mem_normalizeRow x xs).mpr ⟨hx, fun y hy => hm y (List.mem_append_left _ hy)⟩
      · exact List.mem_append_right _ hx
    · intro y hy hxy
      apply hm y _ hxy
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ ((mem_normalizeRow y xs).mp hy).1
      · exact List.mem_append_right _ hy

theorem normalizeRow_append_right (xs ys : List Ty) :
    normalizeRow (xs ++ (normalizeRow ys).elems) = normalizeRow (xs ++ ys) := by
  rw [normalizeRow_append_comm, normalizeRow_append_left, normalizeRow_append_comm ys xs]

theorem normalizeRow_fixed (xs : List Ty) (hs : Effect4.Ascending xs)
    (hm : ∀ x ∈ xs, ∀ y ∈ xs, sub x y = true → sub y x = true) :
    normalizeRow xs = Effect4.Row.mk xs hs := by
  apply Effect4.Row.eq_of_mem_iff
  intro x
  change x ∈ (normalizeRow xs).elems ↔ x ∈ xs
  rw [mem_normalizeRow]
  exact ⟨fun h => h.1, fun hx => ⟨hx, hm x hx⟩⟩

theorem join_eq_ofMembers (a b : Ty) :
    join a b = ofMembers (normalizeRow
      ((normalize a).members ++ (normalize b).members)).elems := rfl

theorem normalize_join (a b : Ty) : normalize (join a b) = join a b :=
  normalize_idem (.union a b)

theorem members_join (a b : Ty) :
    members (join a b) = (normalizeRow
      ((normalize a).members ++ (normalize b).members)).elems := by
  apply members_ofMembers
  intro t ht
  have ht := ((mem_normalizeRow t _).mp ht).1
  exact (List.mem_append.mp ht).elim members_isMember members_isMember

theorem join_comm (a b : Ty) : join a b = join b a := by
  rw [join_eq_ofMembers, join_eq_ofMembers]
  rw [normalizeRow_append_comm]

theorem join_assoc (a b c : Ty) : join (join a b) c = join a (join b c) := by
  rw [join_eq_ofMembers (join a b) c, join_eq_ofMembers a (join b c),
    normalize_join, normalize_join, members_join, members_join]
  rw [normalizeRow_append_left, normalizeRow_append_right, List.append_assoc]

theorem join_self (t : Ty) : join t t = normalize t := by
  rw [join_eq_ofMembers]
  have h := normal_normalize t
  have hr : normalizeRow ((normalize t).members ++ (normalize t).members) =
      Effect4.Row.mk (normalize t).members h.members_ascending := by
    have he : normalizeRow ((normalize t).members ++ (normalize t).members) =
        normalizeRow (normalize t).members :=
      normalizeRow_congr (fun x => by simp only [List.mem_append, or_self])
    rw [he]
    exact normalizeRow_fixed _ h.members_ascending h.members_maximal
  rw [hr]
  exact h.ofMembers_members

theorem join_never (t : Ty) : join .never t = normalize t := by
  rw [join_eq_ofMembers]
  change ofMembers (normalizeRow ([] ++ (normalize t).members)).elems = _
  rw [List.nil_append, normalizeRow_fixed _ (normal_normalize t).members_ascending
    (normal_normalize t).members_maximal]
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
