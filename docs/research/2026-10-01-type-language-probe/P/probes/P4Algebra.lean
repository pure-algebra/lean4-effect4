import P3View

/-!
# Seat P: the subtyping algebra on the copy (type-language probe, 2026-10-01)

Research probe. Copies of `src/Effect4/Laws/Program/TypeAlgebra.lean`'s order theorems at
`bff50631` over `ProbeP.Ty`: `sub_trans_core` (transitivity through the view, no constructor
named), `sub_antisymm_normal` (antisymmetry on normal forms) and `sub_normalize_of_sub` (one of
the eight proofs that follow a function's own case list). Each is marked with what changed.
-/

set_option autoImplicit false

namespace ProbeP.Ty

open ProbeP.Field

/-- copied. -/
private theorem sub_never_core (t : Ty) : sub .never t = true := by
  unfold sub
  split <;> rfl

/-- copied. -/
theorem sub_never_right {a : Ty} (ha : isMember a = true) : sub a .never = false := by
  conv => lhs; unfold sub
  cases a
  case never => exact Bool.noConfusion ha
  case union _ _ => exact Bool.noConfusion ha
  all_goals rfl

/-- copied. -/
theorem isMember_eq_false {t : Ty} (h : isMember t = false) :
    t = .never ∨ ∃ a b, t = .union a b := by
  cases t
  case never => exact Or.inl rfl
  case union a b => exact Or.inr ⟨a, b, rfl⟩
  all_goals exact Bool.noConfusion h

/-- **Transitivity** (`TypeAlgebra.lean:40-114`). With records and maps only, the production text
compiled unchanged (commit `1b069d15`). With the leaf table, the two leaf branches read the table's
laws (`sub_of_leafRule`, `leafRule_trans`, `leafRule_args`, `P3View.lean`) where production
destructures its one literal rule (`litRule_eq_true`); `leafRule_trans` is where the table's
acyclicity enters (a composite of two rules must relate different heads). No edge is named. -/
private theorem sub_trans_core (a b c : Ty) (hab : sub a b = true) (hbc : sub b c = true) :
    sub a c = true := by
  by_cases hac : a = c
  · subst c; exact sub_refl a
  by_cases hcu : c = .unknown
  · subst hcu; exact sub_unknown a
  by_cases habEq : a = b
  · subst b; exact hbc
  by_cases hbcEq : b = c
  · subst c; exact hab
  by_cases ha : isMember a = true
  · by_cases hb : isMember b = true
    · by_cases hc : isMember c = true
      · -- three members, no two equal, and `c` is not the top: the only rules left are the
        -- table's and the congruences
        cases hlac : leafRule a c with
        | true => exact sub_of_leafRule hlac
        | false =>
          cases hlab : leafRule a b with
          | true =>
            -- `a` below `b` by the table: `b` is childless, so `sub b c` is the table's (which
            -- would compose into `a`'s, excluded) or equality (excluded)
            cases hlbc : leafRule b c with
            | true =>
              rw [leafRule_trans hlab hlbc] at hlac
              exact Bool.noConfusion hlac
            | false =>
              rw [sub_eq_args _ _ hb hc hlbc (topRule_eq_false hcu), Bool.and_eq_true_iff] at hbc
              exact absurd (eq_of_sameHead_nil hbc.1 (leafRule_args hlab).2.1) hbcEq
          | false =>
            cases hlbc : leafRule b c with
            | true =>
              -- `b` below `c` by the table: `b` is childless, so `sub a b` forces `a = b`
              rw [sub_eq_args _ _ ha hb hlab (topRule_eq_false (leafRule_ne_unknown hlbc).1),
                Bool.and_eq_true_iff] at hab
              exact absurd (eq_of_sameHead_nil (sameHead_symm hab.1) (leafRule_args hlbc).1).symm habEq
            | false =>
              rw [sub_eq_args _ _ hb hc hlbc (topRule_eq_false hcu), Bool.and_eq_true_iff] at hbc
              have hbu : b ≠ .unknown := by
                rintro rfl
                exact hcu (eq_of_sameHead_nil hbc.1 rfl).symm
              rw [sub_eq_args _ _ ha hb hlab (topRule_eq_false hbu), Bool.and_eq_true_iff] at hab
              rw [sub_eq_args _ _ ha hc hlac (topRule_eq_false hcu), Bool.and_eq_true_iff]
              refine ⟨sameHead_trans hab.1 hbc.1,
                argsBelow_trans hab.1 hbc.1 (fun x y z _ hxy hyz => ?_) hab.2 hbc.2⟩
              exact sub_trans_core x y z hxy hyz
      · -- `c` is a row: nothing but `never` is below the empty union, and a union on the
        -- right is a choice
        rcases isMember_eq_false (Bool.eq_false_iff.mpr hc) with rfl | ⟨c1, c2, rfl⟩
        · rw [sub_never_right hb] at hbc
          exact Bool.noConfusion hbc
        · rw [sub_union_right _ _ _ hb] at hbc
          rw [sub_union_right _ _ _ ha]
          rcases Bool.or_eq_true_iff.mp hbc with h | h
          · exact Bool.or_eq_true_iff.mpr (Or.inl (sub_trans_core a b c1 hab h))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (sub_trans_core a b c2 hab h))
    · -- `b` is a row: the same two shapes in the middle
      rcases isMember_eq_false (Bool.eq_false_iff.mpr hb) with rfl | ⟨b1, b2, rfl⟩
      · rw [sub_never_right ha] at hab
        exact Bool.noConfusion hab
      · rw [sub_union_right _ _ _ ha] at hab
        rw [sub_union_left _ _ _ hbcEq] at hbc
        rcases Bool.and_eq_true_iff.mp hbc with ⟨h1, h2⟩
        rcases Bool.or_eq_true_iff.mp hab with h | h
        · exact sub_trans_core a b1 c h h1
        · exact sub_trans_core a b2 c h h2
  · -- `a` is a row: the empty union is below everything, and a union on the left distributes
    rcases isMember_eq_false (Bool.eq_false_iff.mpr ha) with rfl | ⟨a1, a2, rfl⟩
    · exact sub_never_core c
    · rw [sub_union_left _ _ _ habEq] at hab
      rw [sub_union_left _ _ _ hac]
      rcases Bool.and_eq_true_iff.mp hab with ⟨h1, h2⟩
      exact Bool.and_eq_true_iff.mpr ⟨sub_trans_core a1 b c h1 hbc, sub_trans_core a2 b c h2 hbc⟩
termination_by sizeOf a + sizeOf b + sizeOf c

/-- copied. -/
theorem sub_trans (a b c : Ty) (hab : sub a b = true) (hbc : sub b c = true) :
    sub a c = true := sub_trans_core a b c hab hbc

/-- A declared edge of the leaf table is a rule of the order. -/
theorem sub_of_leafEdge {a b : Ty} {x y : LeafHead} (he : (x, y) ∈ leafEdges)
    (ha : leafHead a = some x) (hb : leafHead b = some y) : sub a b = true :=
  sub_of_leafRule (leafRule_of_edge he ha hb)

/-- **`nat` below `number` follows from the two declared edges** by transitivity; it is not an
entry of the table (`P2Ty.lean`'s guard `!leafEdges.contains (.nat, .number)`). -/
theorem sub_nat_number : sub .nat .number = true :=
  sub_trans .nat .int .number
    (sub_of_leafEdge (x := .nat) (y := .int) (by decide) rfl rfl)
    (sub_of_leafEdge (x := .int) (y := .number) (by decide) rfl rfl)

/-! ## Antisymmetry on normal forms -/

/-- copied. -/
theorem sub_never (t : Ty) : sub .never t = true := by
  unfold sub
  split <;> rfl

/-- copied text (the eliminator's new cases fall to the wildcards). -/
theorem member_sub_self {t x : Ty} (hx : x ∈ t.members) : sub x t = true := by
  induction t with
  | union a b iha ihb =>
    rw [sub_union_right _ _ _ (List.mem_append.mp hx |>.elim members_isMember members_isMember)]
    exact Bool.or_eq_true_iff.mpr ((List.mem_append.mp hx).elim (fun h => Or.inl (iha h))
      (fun h => Or.inr (ihb h)))
  | never => exact absurd hx List.not_mem_nil
  | _ =>
    simp only [members, List.mem_singleton] at hx
    subst x
    exact sub_refl _

/-- rewritten: the production proof's `never` case is `cases x <;> simp_all [...]`. -/
theorem sub_member_right_iff (x t : Ty) (hx : isMember x = true) :
    sub x t = true ↔ ∃ y ∈ t.members, sub x y = true := by
  induction t with
  | union a b iha ihb =>
      rw [sub_union_right _ _ _ hx, Bool.or_eq_true_iff, iha, ihb]
      simp only [members, List.mem_append]
      constructor
      · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
        · exact ⟨y, Or.inl hy, hxy⟩
        · exact ⟨y, Or.inr hy, hxy⟩
      · rintro ⟨y, hy | hy, hxy⟩
        · exact Or.inl ⟨y, hy, hxy⟩
        · exact Or.inr ⟨y, hy, hxy⟩
  | never =>
      rw [sub_never_right hx]
      exact ⟨fun h => Bool.noConfusion h, fun ⟨_, hy, _⟩ => absurd hy List.not_mem_nil⟩
  | _ => simp only [members, List.mem_singleton, exists_eq_left]

/-- copied. -/
theorem sub_iff_members
    (htrans : ∀ a b c, sub a b = true → sub b c = true → sub a c = true)
    (a b : Ty) :
    sub a b = true ↔ ∀ x ∈ a.members, ∃ y ∈ b.members, sub x y = true := by
  constructor
  · intro hab x hx
    exact (sub_member_right_iff x b (members_isMember hx)).mp
      (htrans x a b (member_sub_self hx) hab)
  · intro h
    induction a with
    | never => exact sub_never b
    | union a1 a2 ih1 ih2 =>
        by_cases heq : Ty.union a1 a2 = b
        · subst b; exact sub_refl _
        · rw [sub_union_left _ _ _ heq, Bool.and_eq_true]
          exact ⟨ih1 (fun x hx => h x (List.mem_append_left _ hx)),
            ih2 (fun x hx => h x (List.mem_append_right _ hx))⟩
    | _ =>
        apply (sub_member_right_iff _ b rfl).mpr
        exact h _ List.mem_cons_self

/-- rewritten: the production proof is `cases hn <;> try (simp [...])`. -/
theorem normal_members {t : Ty} (hn : Normal t) :
    ofMembers t.members = t ∧ Effect4.Ascending t.members ∧
      ∀ x ∈ t.members, ∀ y ∈ t.members, sub x y = true → sub y x = true := by
  cases hn
  case never => exact ⟨rfl, List.Pairwise.nil, fun _ hx => absurd hx List.not_mem_nil⟩
  case row r children atoms maximal =>
    rw [members_ofMembers r.elems atoms]
    exact ⟨rfl, r.ascending, maximal⟩
  all_goals
    refine ⟨rfl, List.pairwise_singleton _ _, fun x hx y hy hxy => ?_⟩
    simp only [members, List.mem_singleton] at hx hy
    subst x
    subst y
    exact hxy

/-- copied. -/
theorem sizeOf_member_le {t x : Ty} (hx : x ∈ t.members) : sizeOf x ≤ sizeOf t := by
  induction t with
  | union a b iha ihb =>
    simp only [members, List.mem_append] at hx
    simp only [Ty.union.sizeOf_spec]
    rcases hx with hx | hx
    · have := iha hx; omega
    · have := ihb hx; omega
  | never => exact absurd hx List.not_mem_nil
  | _ =>
    simp only [members, List.mem_singleton] at hx
    subst x
    exact Nat.le_refl _

/-- copied. -/
theorem sizeOf_member_lt {t x : Ty} (hx : x ∈ t.members) (ha : isMember t ≠ true) :
    sizeOf x < sizeOf t := by
  cases t
  case union a b =>
    simp only [members, List.mem_append] at hx
    simp only [Ty.union.sizeOf_spec]
    rcases hx with hx | hx
    · have := sizeOf_member_le hx; omega
    · have := sizeOf_member_le hx; omega
  case never => exact absurd hx List.not_mem_nil
  all_goals exact absurd rfl ha

/-- case: one (a record's children are its canonical fields' types, normal when the record is).
The production proof's non-row cases are one `aesop` call. -/
theorem normal_args {t : Ty} (hn : Normal t) (hm : isMember t = true) :
    ∀ x ∈ t.args.map Prod.snd, Normal x := by
  induction hn with
  | row r children atoms maximal ih =>
    cases hr : r.elems with
    | nil =>
      rw [hr] at hm
      exact Bool.noConfusion hm
    | cons x xs =>
      cases hxs : xs with
      | nil =>
        rw [hr, hxs] at hm
        exact ih x (by rw [hr, hxs]; exact List.mem_cons_self) hm
      | cons y ys =>
        rw [hr, hxs] at hm
        exact Bool.noConfusion hm
  | record hfs hasc =>
    intro x hx
    simp only [args, List.map_map, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact hfs p (mem_canonBy hp)
  | tuple hts _ =>
    intro x hx
    simp only [args, List.map_map, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact hts t ht
  | app hts _ =>
    intro x hx
    simp only [args, List.map_map, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact hts t ht
  | _ => aesop (add norm simp [args])

/-- `sameHead` is symmetric at `false` too. -/
theorem sameHead_false_symm {a b : Ty} (h : sameHead a b = false) : sameHead b a = false := by
  cases hba : sameHead b a with
  | false => rfl
  | true => rw [sameHead_symm hba] at h; exact Bool.noConfusion h

/-- **Antisymmetry on normal forms.** case: the member step reads `argsBelow_antisymm`'s new
conclusion through `Normal.canonHead` (one rewrite); the leaf branches read `leafRule_asymm`, which
is where the table's acyclicity (`leafLe_antisymm`) enters; rewritten: the production
`decreasing_by` closes the member-row calls with `try (apply hsize <;> assumption)`, here two
`have`s at the call sites. Otherwise copied text. -/
theorem sub_antisymm_normal
    (htrans : ∀ a b c, sub a b = true → sub b c = true → sub a c = true)
    (a b : Ty) : Normal a → Normal b →
    sub a b = true → sub b a = true → a = b := by
  intro ha hb hab hba
  by_cases heq : a = b
  · exact heq
  by_cases hatoms : isMember a = true ∧ isMember b = true
  · -- two members, not equal: the table's rule, the top, then one step over `sub_eq_args`
    rcases hatoms with ⟨haAtom, hbAtom⟩
    cases hlab : leafRule a b with
    | true =>
      rw [sub_eq_args _ _ hbAtom haAtom (leafRule_asymm hlab)
        (topRule_eq_false (leafRule_ne_unknown hlab).1), Bool.and_eq_true_iff,
        sameHead_false_symm (leafRule_sameHead hlab)] at hba
      exact Bool.noConfusion hba.1
    | false =>
      cases hlba : leafRule b a with
      | true =>
        rw [sub_eq_args _ _ haAtom hbAtom hlab
          (topRule_eq_false (leafRule_ne_unknown hlba).1), Bool.and_eq_true_iff,
          sameHead_false_symm (leafRule_sameHead hlba)] at hab
        exact Bool.noConfusion hab.1
      | false =>
        have hau : a ≠ .unknown := by
          rintro rfl
          rw [sub_eq_args _ _ haAtom hbAtom hlab
            (topRule_eq_false (fun h => heq h.symm)), Bool.and_eq_true_iff] at hab
          exact heq (eq_of_sameHead_nil hab.1 rfl)
        have hbu : b ≠ .unknown := by
          rintro rfl
          rw [sub_eq_args _ _ hbAtom haAtom hlba
            (topRule_eq_false heq), Bool.and_eq_true_iff] at hba
          exact heq (eq_of_sameHead_nil hba.1 rfl).symm
        rw [sub_eq_args _ _ haAtom hbAtom hlab (topRule_eq_false hbu),
          Bool.and_eq_true_iff] at hab
        rw [sub_eq_args _ _ hbAtom haAtom hlba (topRule_eq_false hau),
          Bool.and_eq_true_iff] at hba
        rw [← Normal.canonHead ha, ← Normal.canonHead hb]
        refine argsBelow_antisymm hab.1 (fun x hx y hy hxy hyx => ?_) hab.2 hba.2
        have hxs : sizeOf x < sizeOf a := sizeOf_args_mem hx
        have hys : sizeOf y < sizeOf b := sizeOf_args_mem hy
        exact sub_antisymm_normal htrans x y (normal_args ha haAtom x hx)
          (normal_args hb hbAtom y hy) hxy hyx
  · have haForm := normal_members ha
    have hbForm := normal_members hb
    have habMembers := (sub_iff_members htrans a b).mp hab
    have hbaMembers := (sub_iff_members htrans b a).mp hba
    have hsize : ∀ x ∈ a.members, ∀ y ∈ b.members,
        sizeOf x + sizeOf y < sizeOf a + sizeOf b := by
      intro x hx y hy
      have hxa := sizeOf_member_le hx
      have hyb := sizeOf_member_le hy
      by_cases hAtomA : isMember a = true
      · have hAtomB : isMember b ≠ true := fun h => hatoms ⟨hAtomA, h⟩
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
        have := hsize x hx y hy
        have hEq := sub_antisymm_normal htrans x y (ha.members hx) (hb.members hy) hxy hyx
        exact hEq ▸ hy
      · intro hy
        obtain ⟨x', hx', hyx'⟩ := hbaMembers x hy
        obtain ⟨z, hz, hx'z⟩ := habMembers x' hx'
        have hzx := hbForm.2.2 x hy z hz (htrans x x' z hyx' hx'z)
        have hx'x := htrans x' z x hx'z hzx
        have := hsize x' hx' x hy
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
  all_goals omega

/-- Antisymmetry, at canonical forms. -/
theorem sub_antisymm (a b : Ty) (ha : Normal a) (hb : Normal b)
    (hab : sub a b = true) (hba : sub b a = true) : a = b :=
  sub_antisymm_normal sub_trans a b ha hb hab hba

/-! ## `sub_normalize_of_sub`: one-way preservation of the raw order by normalization

One of the eight proofs whose case list is a function's own (`fun_cases Ty.sameHead`): two new
cases. The record case reads the canonical fields through `canonBy_map` and `canonBy_idem`
(normalizing a record maps its canonical list) and recurses on corresponding fields. -/

/-- copied. -/
theorem normalizeRow_coverage (xs : List Ty) (x : Ty) (hx : x ∈ xs) :
    ∃ y ∈ (normalizeRow xs).elems, sub x y = true :=
  Effect4.Row.antichain_coverage sub sub_refl sub_trans_core
    (Effect4.Row.normalize xs).elems x ((Effect4.Row.mem_normalize x xs).mpr hx)

/-- copied. -/
theorem members_join (a b : Ty) :
    members (join a b) = (normalizeRow
      ((normalize a).members ++ (normalize b).members)).elems := by
  apply members_ofMembers
  intro t ht
  have ht := ((mem_normalizeRow t _).mp ht).1
  exact (List.mem_append.mp ht).elim members_isMember members_isMember

/-- copied. -/
theorem sub_normalize_union_left (a b : Ty) : sub a.normalize (normalize (.union a b)) = true := by
  apply (sub_iff_members sub_trans _ _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := normalizeRow_coverage _ x (List.mem_append_left b.normalize.members hx)
  exact ⟨y, (members_join a b).symm ▸ hy, hxy⟩

/-- copied. -/
theorem sub_normalize_union_right (a b : Ty) : sub b.normalize (normalize (.union a b)) = true := by
  apply (sub_iff_members sub_trans _ _).mpr
  intro x hx
  obtain ⟨y, hy, hxy⟩ := normalizeRow_coverage _ x (List.mem_append_right a.normalize.members hx)
  exact ⟨y, (members_join a b).symm ▸ hy, hxy⟩

/-- copied. -/
theorem sub_normalize_union_le (a b c : Ty) (hac : sub a.normalize c = true)
    (hbc : sub b.normalize c = true) : sub (normalize (.union a b)) c = true := by
  apply (sub_iff_members sub_trans _ _).mpr
  intro x hx
  have hx' : x ∈ (normalize (.union a b)).members := hx
  rw [show normalize (.union a b) = join a b from rfl, members_join] at hx'
  have hm := ((mem_normalizeRow x _).mp hx').1
  rcases List.mem_append.mp hm with ha | hb
  · exact (sub_iff_members sub_trans _ _).mp hac x ha
  · exact (sub_iff_members sub_trans _ _).mp hbc x hb

/-- copied. -/
theorem members_subset_factors {t x : Ty} (hx : x ∈ t.members) : x ∈ t.factors := by
  cases t with
  | never => exact absurd hx List.not_mem_nil
  | _ => exact hx

/-- copied. -/
theorem normal_factors_nonempty (t : Ty) (ht : Normal t) : ∃ x, x ∈ t.factors := by
  by_cases hnever : t = .never
  · subst t; exact ⟨.never, List.mem_cons_self⟩
  have hnonempty : t.members ≠ [] := by
    intro hempty
    have h := (normal_members ht).1
    rw [hempty] at h
    exact hnever h.symm
  cases hm : t.members with
  | nil => exact (hnonempty hm).elim
  | cons x xs => exact ⟨x, members_subset_factors (by rw [hm]; exact List.mem_cons_self)⟩

/-- copied. -/
theorem factors_coverage (a b : Ty) (hb : Normal b) (hab : sub a b = true)
    (x : Ty) (hx : x ∈ a.factors) : ∃ y ∈ b.factors, sub x y = true := by
  by_cases hnever : a = .never
  · subst a
    have hxn : x = .never := List.mem_singleton.mp hx
    subst x
    obtain ⟨y, hy⟩ := normal_factors_nonempty b hb
    exact ⟨y, hy, sub_never y⟩
  · have hxm : x ∈ a.members := by
      cases a
      case never => exact absurd rfl hnever
      all_goals exact hx
    obtain ⟨y, hy, hxy⟩ := (sub_iff_members sub_trans a b).mp hab x hxm
    exact ⟨y, members_subset_factors hy, hxy⟩

/-- copied. -/
theorem sub_prod_mono (a b c d : Ty) (hac : sub a c = true) (hbd : sub b d = true) :
    sub (.prod a b) (.prod c d) = true := by
  rw [sub_args_prod]
  simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, hac, hbd]

/-- copied. -/
theorem productMembers_isMember {a b p : Ty} (hp : p ∈ productMembers a b) :
    isMember p = true := by
  obtain ⟨x, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hp
  rfl

/-- copied. -/
theorem members_normalize_prod (a b : Ty) :
    (normalize (.prod a b)).members =
      (normalizeRow (productMembers a.normalize b.normalize)).elems := by
  apply members_ofMembers
  intro x hx
  exact productMembers_isMember ((mem_normalizeRow x _).mp hx).1

/-- copied. -/
theorem sub_normalize_prod_mono (a b c d : Ty) (hac : sub a.normalize c.normalize = true)
    (hbd : sub b.normalize d.normalize = true) :
    sub (normalize (.prod a b)) (normalize (.prod c d)) = true := by
  apply (sub_iff_members sub_trans _ _).mpr
  intro p hp
  rw [members_normalize_prod] at hp
  have hp := ((mem_normalizeRow p _).mp hp).1
  obtain ⟨x, hx, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
  obtain ⟨z, hz, hxz⟩ := factors_coverage _ _ (normal_normalize c) hac x hx
  obtain ⟨w, hw, hyw⟩ := factors_coverage _ _ (normal_normalize d) hbd y hy
  have hzw : Ty.prod z w ∈ productMembers c.normalize d.normalize :=
    List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  obtain ⟨q, hq, hzwq⟩ := normalizeRow_coverage _ (.prod z w) hzw
  exact ⟨q, (members_normalize_prod c d).symm ▸ hq,
    sub_trans _ _ _ (sub_prod_mono x y z w hxz hyw) hzwq⟩

/-- new: a record normalizes to its canonical fields with normalized types. -/
theorem normalize_record (fs : List (String × Bool × Ty)) :
    normalize (.record fs) = .record ((canonF fs).map (fun q => (q.1, normPayload q.2))) := by
  rw [normalize, normalizeFields_eq_map, canonBy_map]

/-- A payload map keeps the heads when it keeps every flag. -/
theorem heads_normPayload (l : List (String × Bool × Ty)) :
    heads (l.map (fun q => (q.1, normPayload q.2))) = heads l := by
  simp only [heads, List.map_map]
  rfl

/-- A payload map keeps a list ascending (the order reads names only). -/
theorem ascending_map {β γ : Type} (f : β → γ) {l : List (String × β)} (h : Ascending fieldKey l) :
    Ascending fieldKey (l.map (fun q => (q.1, f q.2))) := by
  unfold Ascending at h ⊢
  rw [List.pairwise_map]
  exact h

/-- new: between two canonical field lists, `sub` is the field-wise comparison. -/
theorem sub_record_of_canonical (cf cg : List (String × Bool × Ty))
    (hcf : Ascending fieldKey cf) (hcg : Ascending fieldKey cg) (hh : heads cf = heads cg)
    (hpairs : ∀ p ∈ cf.zip cg, sub p.1.2.2 p.2.2.2 = true) : sub (.record cf) (.record cg) = true := by
  have hcf' := canonBy_of_ascending cf hcf
  have hcg' := canonBy_of_ascending cg hcg
  have hh' : heads (canonF cf) = heads (canonF cg) := by rw [hcf', hcg']; exact hh
  rw [sub_args_record cf cg hh']
  unfold argsBelow
  simp only [args]
  rw [hcf', hcg', List.zip_map, List.all_map, List.all_eq_true]
  intro p hp
  exact hpairs p hp

/-- new: the record case of `sub_normalize_of_sub`, given the field-wise step. -/
theorem sub_normalize_record (fs gs : List (String × Bool × Ty))
    (hh : heads (canonF fs) = heads (canonF gs))
    (hpair : ∀ p ∈ (canonF fs).zip (canonF gs),
      sub (normalize p.1.2.2) (normalize p.2.2.2) = true) :
    sub (normalize (.record fs)) (normalize (.record gs)) = true := by
  rw [normalize_record, normalize_record]
  apply sub_record_of_canonical _ _ (ascending_map normPayload (canonBy_ascending fs))
    (ascending_map normPayload (canonBy_ascending gs))
  · rw [heads_normPayload, heads_normPayload]
    exact hh
  · intro p hp
    rw [List.zip_map, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hpair q hq

/-- new: the tuple case of `sub_normalize_of_sub`, given the item-wise step. A pair tuple
normalizes as a product; every other arity in place. -/
theorem sub_normalize_tuple (ts us : List Ty) (hlen : ts.length = us.length)
    (hpair : ∀ p ∈ ts.zip us, sub (normalize p.1) (normalize p.2) = true) :
    sub (normalize (.tuple ts)) (normalize (.tuple us)) = true := by
  by_cases h2 : ts.length = 2
  · match ts, us, h2, hlen, hpair with
    | [a1, a2], [b1, b2], _, _, hpair =>
      show sub (normalize (.prod a1 a2)) (normalize (.prod b1 b2)) = true
      exact sub_normalize_prod_mono a1 a2 b1 b2 (hpair (a1, b1) List.mem_cons_self)
        (hpair (a2, b2) (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [normalize_tuple_of_ne ts h2, normalize_tuple_of_ne us (hlen ▸ h2),
      sub_args_tuple _ _ (by rw [normalizeItems_eq_map, normalizeItems_eq_map, List.length_map,
        List.length_map, hlen])]
    unfold argsBelow
    simp only [args]
    rw [normalizeItems_eq_map, normalizeItems_eq_map, List.zip_map, List.all_map, List.zip_map,
      List.all_map, List.all_eq_true]
    intro p hp
    exact hpair p hp

/-- new: the reference case, given the item-wise step both ways (invariant arguments). -/
theorem sub_normalize_app (n : String) (ts us : List Ty) (hlen : ts.length = us.length)
    (hpair : ∀ p ∈ ts.zip us,
      sub (normalize p.1) (normalize p.2) = true ∧ sub (normalize p.2) (normalize p.1) = true) :
    sub (normalize (.app n ts)) (normalize (.app n us)) = true := by
  match ts, us, hlen with
  | [], [], _ => exact sub_refl _
  | t :: ts', u :: us', hlen =>
    rw [normalize_app_of_ne n _ (List.cons_ne_nil _ _), normalize_app_of_ne n _ (List.cons_ne_nil _ _),
      sub_args_app _ _ _ _ ⟨rfl, by rw [normalizeItems_eq_map, normalizeItems_eq_map, List.length_map,
        List.length_map, hlen]⟩]
    unfold argsBelow
    simp only [args]
    rw [normalizeItems_eq_map, normalizeItems_eq_map, List.zip_map, List.all_map, List.zip_map,
      List.all_map, List.all_eq_true]
    intro p hp
    exact Bool.and_eq_true_iff.mpr (hpair p hp)

/-- **One-way preservation of the raw order by normalization.** case: four (record, map, tuple,
reference). The leaf branch reads the table (`leafRule_normalize`, `sub_of_leafRule`); the nine
congruence cases that production closes by `unfold Ty.sub; simp only [hnorm, ↓reduceIte]` read
the view's `sub_args_*` instead, since the unfolded `sub` now carries the table's line. -/
theorem sub_normalize_of_sub (a b : Ty) : sub a b = true → sub a.normalize b.normalize = true := by
  intro hab
  by_cases heq : a = b
  · subst b; exact sub_refl _
  by_cases hbu : b = .unknown
  · subst hbu; exact sub_unknown _
  by_cases hnorm : a.normalize = b.normalize
  · rw [hnorm]; exact sub_refl _
  by_cases ha : isMember a = true
  · by_cases hb : isMember b = true
    · cases hlab : leafRule a b with
      | true =>
        rw [(leafRule_normalize hlab).1, (leafRule_normalize hlab).2]
        exact sub_of_leafRule hlab
      | false =>
        have htop : topRule a b = false := topRule_eq_false hbu
        rw [sub_eq_args a b ha hb hlab htop, Bool.and_eq_true_iff] at hab
        obtain ⟨hhead, hargs⟩ := hab
        revert heq hnorm ha hb hhead hargs
        fun_cases Ty.sameHead a b
        case case1 => intro heq; cases (heq rfl)
        case case2 => intro heq; cases (heq rfl)
        case case3 => intro heq; cases (heq rfl)
        case case4 => intro heq; cases (heq rfl)
        case case5 => intro heq; cases (heq rfl)
        case case6 => intro heq; cases (heq rfl)
        case case7 target1 target2 =>
          intro heq _ _ _ hh
          have : target1 = target2 := of_decide_eq_true hh
          subst this
          cases (heq rfl)
        case case8 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_option]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true]
          exact sub_normalize_of_sub _ _ hargs
        case case9 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_list]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true]
          exact sub_normalize_of_sub _ _ hargs
        case case10 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hargs
          exact sub_normalize_prod_mono _ _ _ _
            (sub_normalize_of_sub _ _ h1)
            (sub_normalize_of_sub _ _ h2)
        case case11 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_except]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true]
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hargs
          exact ⟨sub_normalize_of_sub _ _ h1, sub_normalize_of_sub _ _ h2⟩
        case case12 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_exitOf]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true]
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hargs
          exact ⟨sub_normalize_of_sub _ _ h1, sub_normalize_of_sub _ _ h2⟩
        case case13 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_causeOf]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true]
          exact sub_normalize_of_sub _ _ hargs
        case case14 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_fiberOf]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true]
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hargs
          exact ⟨sub_normalize_of_sub _ _ h1, sub_normalize_of_sub _ _ h2⟩
        case case15 value1 value2 =>
          intro heq _ _ _ hh
          have : value1 = value2 := of_decide_eq_true hh
          subst this
          cases (heq rfl)
        case case16 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_refOf]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true]
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hargs
          exact ⟨sub_normalize_of_sub _ _ h1, sub_normalize_of_sub _ _ h2⟩
        case case17 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_deferredOf]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true]
          obtain ⟨h12, h34⟩ := Bool.and_eq_true_iff.mp hargs
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
          obtain ⟨h3, h4⟩ := Bool.and_eq_true_iff.mp h34
          exact ⟨⟨sub_normalize_of_sub _ _ h1, sub_normalize_of_sub _ _ h2⟩,
            ⟨sub_normalize_of_sub _ _ h3, sub_normalize_of_sub _ _ h4⟩⟩
        case case18 index1 index2 =>
          intro heq _ _ _ hh
          have : index1 = index2 := of_decide_eq_true hh
          subst this
          cases (heq rfl)
        case case19 =>
          intro heq
          cases (heq rfl)
        case case20 fs gs =>
          intro _ _ _ _ hh hargs
          have hh' : heads (canonF fs) = heads (canonF gs) := of_decide_eq_true hh
          apply sub_normalize_record fs gs hh'
          intro p hp
          have hp1 : p.1 ∈ canonF fs := (List.of_mem_zip hp).1
          have hp2 : p.2 ∈ canonF gs := (List.of_mem_zip hp).2
          have := sizeOf_field_lt (mem_canonBy hp1)
          have := sizeOf_field_lt (mem_canonBy hp2)
          have hsub : sub p.1.2.2 p.2.2.2 = true := by
            unfold argsBelow at hargs
            simp only [args] at hargs
            rw [List.zip_map, List.all_map, List.all_eq_true] at hargs
            exact hargs p hp
          exact sub_normalize_of_sub _ _ hsub
        case case21 =>
          intro _ _ _ _ _ hargs
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil, Bool.and_true] at hargs
          dsimp only [normalize]
          rw [sub_args_map]
          simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
            List.all_nil, Bool.and_true, Bool.and_eq_true]
          obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp hargs
          obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
          exact ⟨⟨sub_normalize_of_sub _ _ h1, sub_normalize_of_sub _ _ h2⟩,
            sub_normalize_of_sub _ _ h3⟩
        case case22 ts us =>
          intro _ _ _ _ hh hargs
          have hlen : ts.length = us.length := of_decide_eq_true hh
          apply sub_normalize_tuple ts us hlen
          intro p hp
          have := sizeOf_item_lt (List.of_mem_zip hp).1
          have := sizeOf_item_lt (List.of_mem_zip hp).2
          have hsub : sub p.1 p.2 = true := by
            unfold argsBelow at hargs
            simp only [args] at hargs
            rw [List.zip_map, List.all_map, List.all_eq_true] at hargs
            exact hargs p hp
          exact sub_normalize_of_sub _ _ hsub
        case case23 n ts m us =>
          intro _ _ _ _ hh hargs
          obtain ⟨rfl, hlen⟩ := of_decide_eq_true hh
          apply sub_normalize_app n ts us hlen
          intro p hp
          have := sizeOf_item_lt (List.of_mem_zip hp).1
          have := sizeOf_item_lt (List.of_mem_zip hp).2
          have hsub : sub p.1 p.2 = true ∧ sub p.2 p.1 = true := by
            unfold argsBelow at hargs
            simp only [args] at hargs
            rw [List.zip_map, List.all_map, List.all_eq_true] at hargs
            exact Bool.and_eq_true_iff.mp (hargs p hp)
          exact ⟨sub_normalize_of_sub _ _ hsub.1, sub_normalize_of_sub _ _ hsub.2⟩
        case case24 => intro heq; cases (heq rfl)
        case case25 => intro heq; cases (heq rfl)
        case case26 => intro heq; cases (heq rfl)
        case case27 => intro heq; cases (heq rfl)
        case case28 =>
          intro _ _ _ _ hh
          cases hh
    · -- `b` is a row: nothing but `never` is below the empty union
      rcases isMember_eq_false (Bool.eq_false_iff.mpr hb) with rfl | ⟨b1, b2, rfl⟩
      · rw [sub_never_right ha] at hab
        exact Bool.noConfusion hab
      · rw [sub_union_right _ _ _ ha, Bool.or_eq_true_iff] at hab
        rcases hab with h | h
        · exact sub_trans _ _ _ (sub_normalize_of_sub a b1 h)
            (sub_normalize_union_left b1 b2)
        · exact sub_trans _ _ _ (sub_normalize_of_sub a b2 h)
            (sub_normalize_union_right b1 b2)
  · rcases isMember_eq_false (Bool.eq_false_iff.mpr ha) with rfl | ⟨a1, a2, rfl⟩
    · exact sub_never b.normalize
    · rw [sub_union_left _ _ _ heq, Bool.and_eq_true] at hab
      exact sub_normalize_union_le a1 a2 b.normalize
        (sub_normalize_of_sub a1 b hab.1) (sub_normalize_of_sub a2 b hab.2)
termination_by sizeOf a + sizeOf b
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end ProbeP.Ty

#print axioms ProbeP.Ty.sub_trans
#print axioms ProbeP.Ty.sub_nat_number
#print axioms ProbeP.Ty.sub_member_right_iff
#print axioms ProbeP.Ty.sub_iff_members
#print axioms ProbeP.Ty.normal_members
#print axioms ProbeP.Ty.normal_args
#print axioms ProbeP.Ty.sub_antisymm_normal
#print axioms ProbeP.Ty.sub_antisymm
#print axioms ProbeP.Ty.normalize_record
#print axioms ProbeP.Ty.sub_normalize_record
#print axioms ProbeP.Ty.sub_normalize_tuple
#print axioms ProbeP.Ty.sub_normalize_app
#print axioms ProbeP.Ty.sub_normalize_of_sub
