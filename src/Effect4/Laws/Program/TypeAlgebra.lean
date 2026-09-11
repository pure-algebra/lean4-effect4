import Effect4.Program.Typed

namespace Effect4.Program.Ty

private theorem sub_never_core (t : Ty) : sub .never t = true := by
  unfold sub
  split <;> rfl

/-- Absorption and the canonical order use the same structural transitivity proof. -/
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

/-- Raw structural subtyping is transitive; distribution remains in normalization. -/
theorem sub_trans (a b c : Ty) (hab : sub a b = true) (hbc : sub b c = true) :
    sub a c = true := sub_trans_core a b c hab hbc

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

namespace Effect4.Program.Ty.OrderProof
open Effect4 Effect4.Program

theorem sub_never (t : Ty) : Ty.sub .never t = true := by
  unfold Ty.sub
  split <;> rfl

theorem member_sub_self {t x : Ty} (hx : x ∈ t.members) : Ty.sub x t = true := by
  induction t <;> simp only [Ty.members, List.mem_append, List.mem_singleton] at hx
  all_goals try contradiction
  all_goals try (subst x; exact Ty.sub_refl _)
  case union a b iha ihb =>
    rw [Ty.sub_union_right _ _ _ (hx.elim Ty.members_isMember Ty.members_isMember)]
    exact Bool.or_eq_true_iff.mpr (hx.elim (fun h => Or.inl (iha h)) (fun h => Or.inr (ihb h)))

theorem sub_member_right_iff (x t : Ty) (hx : Ty.isMember x = true) :
    Ty.sub x t = true ↔ ∃ y ∈ t.members, Ty.sub x y = true := by
  induction t with
  | union a b iha ihb =>
      rw [Ty.sub_union_right _ _ _ hx, Bool.or_eq_true_iff, iha, ihb]
      simp only [Ty.members, List.mem_append]
      constructor
      · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
        · exact ⟨y, Or.inl hy, hxy⟩
        · exact ⟨y, Or.inr hy, hxy⟩
      · rintro ⟨y, hy | hy, hxy⟩
        · exact Or.inl ⟨y, hy, hxy⟩
        · exact Or.inr ⟨y, hy, hxy⟩
  | never =>
      cases x <;> simp_all [Ty.isMember, Ty.sub, Ty.members]
  | _ => simp only [Ty.members, List.mem_singleton, exists_eq_left]

theorem sub_iff_members
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : Ty) :
    Ty.sub a b = true ↔ ∀ x ∈ a.members, ∃ y ∈ b.members, Ty.sub x y = true := by
  constructor
  · intro hab x hx
    exact (sub_member_right_iff x b (Ty.members_isMember hx)).mp
      (htrans x a b (member_sub_self hx) hab)
  · intro h
    induction a with
    | never => exact sub_never b
    | union a1 a2 ih1 ih2 =>
        by_cases heq : Ty.union a1 a2 = b
        · subst b; exact Ty.sub_refl _
        · rw [Ty.sub_union_left _ _ _ heq, Bool.and_eq_true]
          exact ⟨ih1 (fun x hx => h x (List.mem_append_left _ hx)),
            ih2 (fun x hx => h x (List.mem_append_right _ hx))⟩
    | _ =>
        apply (sub_member_right_iff _ b rfl).mpr
        exact h _ List.mem_cons_self

theorem normal_members {t : Ty} (hn : Ty.Normal t) :
    Ty.ofMembers t.members = t ∧ Ascending t.members ∧
      ∀ x ∈ t.members, ∀ y ∈ t.members, Ty.sub x y = true → Ty.sub y x = true := by
  cases hn <;> try (simp [Ty.members, Ty.ofMembers, Ascending])
  case row r children atoms maximal =>
    rw [Ty.members_ofMembers r.elems atoms]
    exact ⟨rfl, r.ascending, maximal⟩

theorem normal_children (t : Ty) : Ty.Normal t →
    match t with
    | .option a | .list a | .causeOf a => Ty.Normal a
    | .prod a b | .except a b | .exitOf a b | .fiberOf a b => Ty.Normal a ∧ Ty.Normal b
    | _ => True := by
  intro hn
  induction hn with
  | option h _ | list h _ | causeOf h _ => exact h
  | prod ha hb _ _ _ _ | except ha hb _ _ | exitOf ha hb _ _ | fiberOf ha hb _ _ =>
      exact ⟨ha, hb⟩
  | row r children atoms maximal ih =>
      cases hr : r.elems with
      | nil => simp [Ty.ofMembers]
      | cons x xs =>
          cases xs with
          | nil =>
              simpa only [hr, Ty.ofMembers] using ih x (by rw [hr]; exact List.mem_cons_self)
          | cons y ys => simp [Ty.ofMembers]
  | _ => trivial

theorem sizeOf_member_le {t x : Ty} (hx : x ∈ t.members) : sizeOf x ≤ sizeOf t := by
  induction t <;> simp only [Ty.members, List.mem_append, List.mem_singleton] at hx
  all_goals try contradiction
  all_goals try (subst x; exact Nat.le_refl _)
  case union a b iha ihb =>
    simp only [Ty.union.sizeOf_spec]
    rcases hx with hx | hx
    · have := iha hx; omega
    · have := ihb hx; omega

theorem sizeOf_member_lt {t x : Ty} (hx : x ∈ t.members) (ha : Ty.isMember t ≠ true) :
    sizeOf x < sizeOf t := by
  cases t <;> simp only [Ty.isMember] at ha <;> try contradiction
  case union a b =>
    simp only [Ty.members, List.mem_append] at hx
    simp only [Ty.union.sizeOf_spec]
    rcases hx with hx | hx
    · have := sizeOf_member_le hx; omega
    · have := sizeOf_member_le hx; omega

theorem sub_antisymm_normal
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : Ty) : Ty.Normal a → Ty.Normal b →
    Ty.sub a b = true → Ty.sub b a = true → a = b := by
  intro ha hb hab hba
  by_cases heq : a = b
  · exact heq
  by_cases hatoms : Ty.isMember a = true ∧ Ty.isMember b = true
  · rcases hatoms with ⟨haAtom, hbAtom⟩
    have hca := normal_children a ha
    have hcb := normal_children b hb
    cases a <;> cases b <;> simp only [Ty.isMember] at haAtom hbAtom <;> try contradiction
    all_goals
      unfold Ty.sub at hab hba
      simp only [heq, Ne.symm heq, ↓reduceIte, Bool.and_eq_true, Bool.false_eq_true] at hab hba
    all_goals
      first
      | exact congrArg _ (sub_antisymm_normal htrans _ _ hca hcb hab hba)
      | have h1 := sub_antisymm_normal htrans _ _ hca.1 hcb.1 hab.1 hba.1
        have h2 := sub_antisymm_normal htrans _ _ hca.2 hcb.2 hab.2 hba.2
        cases h1
        cases h2
        rfl
  · have haForm := normal_members ha
    have hbForm := normal_members hb
    have habMembers := (sub_iff_members htrans a b).mp hab
    have hbaMembers := (sub_iff_members htrans b a).mp hba
    have hsize : ∀ x ∈ a.members, ∀ y ∈ b.members,
        sizeOf x + sizeOf y < sizeOf a + sizeOf b := by
      intro x hx y hy
      have hxa := sizeOf_member_le hx
      have hyb := sizeOf_member_le hy
      by_cases hAtomA : Ty.isMember a = true
      · have hAtomB : Ty.isMember b ≠ true := fun h => hatoms ⟨hAtomA, h⟩
        have := sizeOf_member_lt hy hAtomB
        omega
      · have := sizeOf_member_lt hx hAtomA
        omega
    have hmem : ∀ x, x ∈ a.members ↔ x ∈ b.members := by
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, hxy⟩ := habMembers x hx
        obtain ⟨z, hz, hyz⟩ := hbaMembers y hy
        have hzx := haForm.2.2 x hx z hz (htrans x y z hxy hyz)
        have hyx := htrans y z x hyz hzx
        have hEq := sub_antisymm_normal htrans x y (ha.members hx) (hb.members hy) hxy hyx
        exact hEq ▸ hy
      · intro hy
        obtain ⟨x', hx', hyx'⟩ := hbaMembers x hy
        obtain ⟨z, hz, hx'z⟩ := habMembers x' hx'
        have hzx := hbForm.2.2 x hy z hz (htrans x x' z hyx' hx'z)
        have hx'x := htrans x' z x hx'z hzx
        have hEq := sub_antisymm_normal htrans x' x (ha.members hx') (hb.members hy) hx'x hyx'
        exact hEq ▸ hx'
    have hrows : (⟨a.members, haForm.2.1⟩ : Effect4.Row Ty) = ⟨b.members, hbForm.2.1⟩ :=
      Effect4.Row.eq_of_mem_iff hmem
    have hlist : a.members = b.members := congrArg Effect4.Row.elems hrows
    rw [← haForm.1, ← hbForm.1, hlist]
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try (apply hsize <;> assumption)

theorem sub_antisymm_canonical
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : CTy) (hab : Ty.sub a.toRaw b.toRaw = true)
    (hba : Ty.sub b.toRaw a.toRaw = true) : a = b := by
  apply Subtype.ext
  apply sub_antisymm_normal htrans a.val b.val
  · exact a.property ▸ Ty.normal_normalize a.val
  · exact b.property ▸ Ty.normal_normalize b.val
  · exact hab
  · exact hba

theorem members_join (a b : CTy) :
    (CTy.join a b).toRaw.members =
      (Ty.normalizeRow (a.toRaw.members ++ b.toRaw.members)).elems := by
  change (Ty.ofMembers (Ty.normalizeRow
    (a.val.normalize.members ++ b.val.normalize.members)).elems).members = _
  rw [a.property, b.property]
  apply Ty.members_ofMembers
  intro x hx
  have hm := ((Ty.mem_normalizeRow x _).mp hx).1
  exact (List.mem_append.mp hm).elim Ty.members_isMember Ty.members_isMember

theorem normalizeRow_coverage
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (xs : List Ty) (x : Ty) (hx : x ∈ xs) :
    ∃ y ∈ (Ty.normalizeRow xs).elems, Ty.sub x y = true := by
  apply Effect4.Row.antichain_coverage Ty.sub Ty.sub_refl htrans (Row.normalize xs).elems x
  exact (Row.mem_normalize x xs).mpr hx

theorem sub_join_left
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : CTy) : Ty.sub a.toRaw (CTy.join a b).toRaw = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := normalizeRow_coverage htrans _ x (List.mem_append_left b.toRaw.members hx)
  exact ⟨y, (members_join a b).symm ▸ hy, hxy⟩

theorem sub_join_right
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : CTy) : Ty.sub b.toRaw (CTy.join a b).toRaw = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := normalizeRow_coverage htrans _ x (List.mem_append_right a.toRaw.members hx)
  exact ⟨y, (members_join a b).symm ▸ hy, hxy⟩

theorem join_least
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b c : CTy) (hac : Ty.sub a.toRaw c.toRaw = true)
    (hbc : Ty.sub b.toRaw c.toRaw = true) : Ty.sub (CTy.join a b).toRaw c.toRaw = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro x hx
  rw [members_join] at hx
  have hm := ((Ty.mem_normalizeRow x _).mp hx).1
  rcases List.mem_append.mp hm with ha | hb
  · exact (sub_iff_members htrans _ _).mp hac x ha
  · exact (sub_iff_members htrans _ _).mp hbc x hb

theorem sub_join_iff
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b c : CTy) :
    Ty.sub (CTy.join a b).toRaw c.toRaw = true ↔
      Ty.sub a.toRaw c.toRaw = true ∧ Ty.sub b.toRaw c.toRaw = true := by
  constructor
  · intro h
    exact ⟨htrans _ _ _ (sub_join_left htrans a b) h,
      htrans _ _ _ (sub_join_right htrans a b) h⟩
  · intro ⟨ha, hb⟩
    exact join_least htrans a b c ha hb

theorem members_normalize_union (a b : Ty) :
    (Ty.normalize (.union a b)).members =
      (Ty.normalizeRow (a.normalize.members ++ b.normalize.members)).elems :=
  Ty.members_join a b

theorem sub_normalize_union_left
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : Ty) : Ty.sub a.normalize (Ty.normalize (.union a b)) = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Ty.normalizeRow_coverage _ x
    (List.mem_append_left b.normalize.members hx)
  exact ⟨y, (members_normalize_union a b).symm ▸ hy, hxy⟩

theorem sub_normalize_union_right
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : Ty) : Ty.sub b.normalize (Ty.normalize (.union a b)) = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Ty.normalizeRow_coverage _ x
    (List.mem_append_right a.normalize.members hx)
  exact ⟨y, (members_normalize_union a b).symm ▸ hy, hxy⟩

theorem sub_normalize_union_le
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b c : Ty) (hac : Ty.sub a.normalize c = true) (hbc : Ty.sub b.normalize c = true) :
    Ty.sub (Ty.normalize (.union a b)) c = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro x hx
  rw [members_normalize_union] at hx
  have hm := ((Ty.mem_normalizeRow x _).mp hx).1
  rcases List.mem_append.mp hm with ha | hb
  · exact (sub_iff_members htrans _ _).mp hac x ha
  · exact (sub_iff_members htrans _ _).mp hbc x hb

theorem members_subset_factors {t x : Ty} (hx : x ∈ t.members) : x ∈ t.factors := by
  cases t with
  | never => cases hx
  | _ => exact hx

theorem normal_factors_nonempty (t : Ty) (ht : Ty.Normal t) : ∃ x, x ∈ t.factors := by
  by_cases hnever : t = .never
  · subst t; exact ⟨.never, List.mem_cons_self⟩
  have hnonempty : t.members ≠ [] := by
    intro hempty
    have h := ht.ofMembers_members
    rw [hempty] at h
    exact hnever h.symm
  cases hm : t.members with
  | nil => exact (hnonempty hm).elim
  | cons x xs =>
      exact ⟨x, members_subset_factors (by rw [hm]; exact List.mem_cons_self)⟩

theorem factors_coverage
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : Ty) (hb : Ty.Normal b) (hab : Ty.sub a b = true)
    (x : Ty) (hx : x ∈ a.factors) : ∃ y ∈ b.factors, Ty.sub x y = true := by
  by_cases hnever : a = .never
  · subst a
    have hxn : x = .never := List.mem_singleton.mp hx
    subst x
    obtain ⟨y, hy⟩ := normal_factors_nonempty b hb
    exact ⟨y, hy, sub_never y⟩
  · have hxm : x ∈ a.members := by
      cases a <;> try contradiction
      all_goals exact hx
    obtain ⟨y, hy, hxy⟩ := (sub_iff_members htrans a b).mp hab x hxm
    exact ⟨y, members_subset_factors hy, hxy⟩

theorem sub_prod_mono (a b c d : Ty) (hac : Ty.sub a c = true) (hbd : Ty.sub b d = true) :
    Ty.sub (.prod a b) (.prod c d) = true := by
  by_cases heq : Ty.prod a b = .prod c d
  · rw [heq]; exact Ty.sub_refl _
  · rw [Ty.sub_prod_of_ne _ _ _ _ heq, Bool.and_eq_true]
    exact ⟨hac, hbd⟩

theorem productMembers_isMember {a b p : Ty} (hp : p ∈ Ty.productMembers a b) :
    Ty.isMember p = true := by
  obtain ⟨x, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem members_normalize_prod (a b : Ty) :
    (Ty.normalize (.prod a b)).members =
      (Ty.normalizeRow (Ty.productMembers a.normalize b.normalize)).elems := by
  apply Ty.members_ofMembers
  intro x hx
  exact productMembers_isMember ((Ty.mem_normalizeRow x _).mp hx).1

theorem sub_normalize_prod_mono
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b c d : Ty) (hac : Ty.sub a.normalize c.normalize = true)
    (hbd : Ty.sub b.normalize d.normalize = true) :
    Ty.sub (Ty.normalize (.prod a b)) (Ty.normalize (.prod c d)) = true := by
  apply (sub_iff_members htrans _ _).mpr
  intro p hp
  rw [members_normalize_prod] at hp
  have hp := ((Ty.mem_normalizeRow p _).mp hp).1
  obtain ⟨x, hx, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
  obtain ⟨z, hz, hxz⟩ := factors_coverage htrans _ _ (Ty.normal_normalize c) hac x hx
  obtain ⟨w, hw, hyw⟩ := factors_coverage htrans _ _ (Ty.normal_normalize d) hbd y hy
  have hzw : Ty.prod z w ∈ Ty.productMembers c.normalize d.normalize :=
    List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  obtain ⟨q, hq, hzwq⟩ := Ty.normalizeRow_coverage _ (.prod z w) hzw
  exact ⟨q, (members_normalize_prod c d).symm ▸ hq,
    htrans _ _ _ (sub_prod_mono x y z w hxz hyw) hzwq⟩

theorem sub_normalize_of_sub
    (htrans : ∀ a b c, Ty.sub a b = true → Ty.sub b c = true → Ty.sub a c = true)
    (a b : Ty) : Ty.sub a b = true → Ty.sub a.normalize b.normalize = true := by
  intro hab
  by_cases heq : a = b
  · subst b; exact Ty.sub_refl _
  by_cases hnorm : a.normalize = b.normalize
  · rw [hnorm]; exact Ty.sub_refl _
  by_cases ha : Ty.isMember a = true
  · by_cases hb : Ty.isMember b = true
    · cases a <;> cases b <;> simp only [Ty.isMember] at ha hb <;> try contradiction
      all_goals
        unfold Ty.sub at hab
        simp only [heq, ↓reduceIte, Bool.and_eq_true, Bool.false_eq_true] at hab
      all_goals
        first
        | exact sub_normalize_prod_mono htrans _ _ _ _
            (sub_normalize_of_sub htrans _ _ hab.1) (sub_normalize_of_sub htrans _ _ hab.2)
        | exact Ty.sub_lit_string _
        | simp only [Ty.normalize] at hnorm ⊢
          unfold Ty.sub
          simp only [hnorm, ↓reduceIte, Bool.and_eq_true]
          first
          | exact sub_normalize_of_sub htrans _ _ hab
          | exact ⟨sub_normalize_of_sub htrans _ _ hab.1, sub_normalize_of_sub htrans _ _ hab.2⟩
    · cases b <;> simp only [Ty.isMember] at hb <;> try contradiction
      case never =>
        cases a <;> simp only [Ty.isMember] at ha <;> try contradiction
        all_goals
          unfold Ty.sub at hab
          simp only [heq, ↓reduceIte, Bool.false_eq_true] at hab
      case union b1 b2 =>
        rw [Ty.sub_union_right _ _ _ ha, Bool.or_eq_true_iff] at hab
        rcases hab with h | h
        · exact htrans _ _ _ (sub_normalize_of_sub htrans a b1 h)
            (sub_normalize_union_left htrans b1 b2)
        · exact htrans _ _ _ (sub_normalize_of_sub htrans a b2 h)
            (sub_normalize_union_right htrans b1 b2)
  · cases a <;> simp only [Ty.isMember] at ha <;> try contradiction
    case never => exact sub_never b.normalize
    case union a1 a2 =>
      rw [Ty.sub_union_left _ _ _ heq, Bool.and_eq_true] at hab
      exact sub_normalize_union_le htrans a1 a2 b.normalize
        (sub_normalize_of_sub htrans a1 b hab.1) (sub_normalize_of_sub htrans a2 b hab.2)
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega


end Effect4.Program.Ty.OrderProof

namespace Effect4.Program.Ty

theorem sub_antisymm_canonical (a b : CTy)
    (hab : sub a.toRaw b.toRaw = true) (hba : sub b.toRaw a.toRaw = true) : a = b :=
  OrderProof.sub_antisymm_canonical sub_trans a b hab hba

theorem sub_join_left (a b : CTy) : sub a.toRaw (CTy.join a b).toRaw = true :=
  OrderProof.sub_join_left sub_trans a b

theorem sub_join_right (a b : CTy) : sub b.toRaw (CTy.join a b).toRaw = true :=
  OrderProof.sub_join_right sub_trans a b

theorem join_least (a b c : CTy) (hac : sub a.toRaw c.toRaw = true)
    (hbc : sub b.toRaw c.toRaw = true) : sub (CTy.join a b).toRaw c.toRaw = true :=
  OrderProof.join_least sub_trans a b c hac hbc

/-- One-way preservation of the raw relation by normalization. No converse is asserted. -/
theorem sub_normalize_of_sub (a b : Ty) (hab : sub a b = true) :
    sub a.normalize b.normalize = true := OrderProof.sub_normalize_of_sub sub_trans a b hab

end Effect4.Program.Ty

namespace Effect4.Program.CTy

instance instIsPartialOrder : Std.IsPartialOrder CTy where
  le_refl t := Ty.sub_refl t.toRaw
  le_trans a b c := Ty.sub_trans a.toRaw b.toRaw c.toRaw
  le_antisymm := Ty.sub_antisymm_canonical

instance instLawfulOrderLT : Std.LawfulOrderLT CTy where
  lt_iff _ _ := Iff.rfl

/-- Canonical union is the least upper bound in the public subtype order. -/
instance instLawfulOrderSup : Std.LawfulOrderSup CTy where
  max_le_iff := Ty.OrderProof.sub_join_iff Ty.sub_trans

/-- The empty canonical union is below every canonical type. -/
theorem never_le (t : CTy) : never ≤ t := Ty.OrderProof.sub_never t.toRaw

end Effect4.Program.CTy
