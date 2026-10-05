import Effect4.Laws.Program.TyView

/-!
# The fold condition for the subtype order (tooling plan 1.5)

`Val.hasTy` is a fold (`fold_of` at `src/Effect4/Laws/Program/Folds/Ty.lean`), so "membership respects
`sub`" is not a fact about `Val.hasTy` at all: it is a fact about *any* admission algebra whose
arms satisfy the generated condition `AdmitsSub` (`Laws/Program/TyView.lean`, one field per
constructor). Three declarations, in the order they depend on each other:

* `cata_admits_sub` — the law, proved once, by `fun_induction Ty.sub`, naming no constructor;
* `Val.hasTy_admitsSub` — the fourteen fields discharged for the admission fold of this tree;
* `hasTy_sub` — the law every caller uses, now the two applied to one another.

`hasTy_sub` lives here rather than in the core beside `Val.hasTy` because the fold lives above
the core (`Program/Folds/Ty.lean` imports `Program/Typed.lean`), and because the core keeps
definitions while the Laws keep laws: `Program/Typed.lean` carries no theorem about `sub` any
more. Every call site is under `Laws`, and all but two of them reach this module through
`Effect4.Laws.Program.TypeAlgebra`.

The carrier is the paramorphic one `fold_of` builds — `Ty × (Val → List String → Bool)`, the node
rebuilt beside its result — so every field reads the arm's `.2`. `Val.hasTy.eq_cata` is
`Val.hasTy v ty allocated = (cata_ty Val.hasTy.alg ty).snd v allocated`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine Effect4.Program.Ty

/-! ## The leaf table's rule, through the edge fields (decisions row 177)

`AdmitsSub` carries one inclusion per declared edge; the closure is `Adm.le_trans` along a path of
the table (`leafLe_iff_path`), and no edge enters a literal, so a literal's payload rides along
unread past the first step. No pair of heads is named here but the four edges, once each. -/

/-- A leaf head's type, a literal's at a given payload. -/
def leafTy : Ty.LeafHead → String → Ty
  | .lit, s => .lit s
  | .string, _ => .string
  | .nat, _ => .nat
  | .int, _ => .int
  | .number, _ => .number
  | .undefined, _ => .undefined
  | .unit, _ => .unit

theorem leafTy_of_head {t : Ty} {x : Ty.LeafHead} (h : Ty.leafHead t = some x) :
    ∃ s, t = leafTy x s := by
  cases t
  case lit s => cases h; exact ⟨s, rfl⟩
  case string | nat | int | number | undefined | unit => cases h; exact ⟨"", rfl⟩
  all_goals cases h

theorem leafTy_payload {y : Ty.LeafHead} (hy : y ≠ .lit) (s s' : String) :
    leafTy y s = leafTy y s' := by
  cases y
  case lit => exact absurd rfl hy
  all_goals rfl

/-- **One inclusion per declared edge**, read off the condition's edge fields. -/
theorem admits_edge {alg : TyAlgebra AdmCarrier} (h : AdmitsSub alg) {x y : Ty.LeafHead}
    (he : (x, y) ∈ Ty.leafEdges) (s : String) :
    Adm.le (cata_ty alg (leafTy x s)).2 (cata_ty alg (leafTy y s)).2 := by
  simp only [Ty.leafEdges, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.lit_string s
  · exact h.nat_int
  · exact h.int_number
  · exact h.undefined_unit

/-- The closure: an inclusion along every path of the table. -/
theorem admits_path {alg : TyAlgebra AdmCarrier} (h : AdmitsSub alg) {x y : Ty.LeafHead}
    (hp : Ty.LeafPath Ty.leafEdges x y) (s : String) :
    Adm.le (cata_ty alg (leafTy x s)).2 (cata_ty alg (leafTy y s)).2 := by
  induction hp with
  | refl => exact Adm.le_refl _
  | step he _ ih => exact Adm.le_trans (admits_edge h he s) ih

/-- No declared edge enters a literal, so a path that moves ends at a head with no payload. -/
theorem leafPath_target_ne_lit {x y : Ty.LeafHead} (hp : Ty.LeafPath Ty.leafEdges x y)
    (hxy : x ≠ y) : y ≠ .lit := by
  have hall : ∀ e ∈ Ty.leafEdges, e.2 ≠ .lit := by decide
  induction hp with
  | refl => exact absurd rfl hxy
  | step he hp ih =>
    rename_i x z y
    by_cases hzy : z = y
    · subst hzy
      exact hall _ he
    · exact ih hzy

/-- **The table's rule is an inclusion for every algebra with the order's condition.** -/
theorem cata_admits_leafRule {alg : TyAlgebra AdmCarrier} (h : AdmitsSub alg) {a b : Ty}
    (hl : Ty.leafRule a b = true) : Adm.le (cata_ty alg a).2 (cata_ty alg b).2 := by
  obtain ⟨x, y, hx, hy, hxy, hle⟩ := Ty.leafRule_eq_true hl
  have hp := Ty.leafLe_iff_path.mp hle
  obtain ⟨s, rfl⟩ := leafTy_of_head hx
  obtain ⟨s', rfl⟩ := leafTy_of_head hy
  rw [leafTy_payload (leafPath_target_ne_lit hp hxy) s' s]
  exact admits_path h hp s

/-! ## The one real proof

By `fun_induction Ty.sub`, so the case list is `sub`'s own arm list: the reflexive guard, the
leaf table's line, four exceptional rules, the congruence arms and a catch-all whose hypothesis
is `false = true`. No constructor of `Ty` is named by the script; each case cites the field of
`AdmitsSub` that carries it. -/

theorem cata_admits_sub {alg : TyAlgebra AdmCarrier} (h : AdmitsSub alg) {a b : Ty}
    (hsub : Ty.sub a b = true) : Adm.le (cata_ty alg a).2 (cata_ty alg b).2 := by
  fun_induction Ty.sub a b
  -- the reflexive guard
  case case1 => exact Adm.le_refl _
  -- the leaf table's line (decisions row 177)
  case case2 _ _ _ hl => exact cata_admits_leafRule h hl
  -- `never` admits nothing, so the inclusion is vacuous
  case case3 =>
    intro v al hp
    simp only [cata_ty, h.never] at hp
    exact Bool.noConfusion hp
  -- a union on the left is the disjunction of its members
  case case4 a1 a2 b _ _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al hp
    simp only [cata_ty, h.union] at hp
    exact (Bool.or_eq_true_iff.mp hp).elim (fun hx => iha h1 v al hx) (fun hx => ihb h2 v al hx)
  -- a union on the right is a choice
  case case5 a b1 b2 _ _ _ _ iha ihb =>
    intro v al hp
    simp only [cata_ty, h.union]
    exact (Bool.or_eq_true_iff.mp hsub).elim
      (fun hx => Bool.or_eq_true_iff.mpr (Or.inl (iha hx v al hp)))
      (fun hx => Bool.or_eq_true_iff.mpr (Or.inr (ihb hx v al hp)))
  -- the top admits everything (decisions row 46)
  case case6 =>
    intro v al _
    simp only [cata_ty]
    exact h.top v al
  -- the congruence arms, each its own field
  case case7 x y _ _ ih => simp only [cata_ty]; exact h.option _ _ (ih hsub)
  case case8 x y _ _ ih => simp only [cata_ty]; exact h.list _ _ (ih hsub)
  case case9 a1 a2 b1 b2 _ _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.prod _ _ _ _ (iha h1) (ihb h2)
  case case10 e1 a1 e2 a2 _ _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.except _ _ _ _ (ihe h1) (iha h2)
  case case11 a1 e1 a2 e2 _ _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.exitOf _ _ _ _ (iha h1) (ihe h2)
  case case12 e1 e2 _ _ ih => simp only [cata_ty]; exact h.causeOf _ _ (ih hsub)
  case case13 a1 e1 a2 e2 _ _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.fiberOf _ _ _ _ (iha h1) (ihe h2)
  -- the invariant handles (decisions row 55): both directions, from the arm's two comparisons
  case case14 a1 a2 _ _ ih12 ih21 =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [cata_ty]
    exact h.refOf _ _ ⟨ih12 h1, ih21 h2⟩
  case case15 a1 e1 a2 e2 _ _ iha12 iha21 ihe12 ihe21 =>
    obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    simp only [cata_ty]
    exact h.deferredOf _ _ _ _ ⟨iha12 h1, iha21 h2⟩ ⟨ihe12 h3, ihe21 h4⟩
  -- the variable-arity heads (decisions rows 119, 125, 158, 159)
  case case16 fs gs _ _ ih =>
    obtain ⟨hh, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hall' : ((Ty.canon fs).zip (Ty.canon gs)).all (fun pq => Ty.sub pq.1.2.2 pq.2.2.2) = true := by
      rw [← Ty.all_attach_eq]
      exact hall
    rw [List.all_eq_true] at hall'
    simp only [cata_ty_record]
    have hpm : prodMapSnd (prodMapSnd (cata_ty alg)) =
        fun q : String × Bool × Ty => (q.1, prodMapSnd (cata_ty alg) q.2) := rfl
    refine h.record _ _ ?_ ?_
    · rw [hpm, Ty.canon, Ty.canon, Field.canonBy_map, Field.canonBy_map, List.map_map, List.map_map]
      exact of_decide_eq_true hh
    · rw [hpm, Ty.canon, Ty.canon, Field.canonBy_map, Field.canonBy_map, List.zip_map]
      intro p q hpq
      rw [List.mem_map] at hpq
      obtain ⟨⟨f, g⟩, hfg, hpq⟩ := hpq
      cases hpq
      exact ih (f, g) hfg (hall' (f, g) hfg)
  case case17 k1 v1 k2 v2 _ _ ihk12 ihk21 ihv =>
    obtain ⟨hk, hv⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨h12, h21⟩ := Bool.and_eq_true_iff.mp hk
    simp only [cata_ty]
    exact h.map _ _ _ _ ⟨ihk12 h12, ihk21 h21⟩ (ihv hv)
  case case18 xs ys _ _ ih =>
    obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hall' : (xs.zip ys).all (fun pq => Ty.sub pq.1 pq.2) = true := by
      rw [← Ty.all_attach_eq]
      exact hall
    rw [List.all_eq_true] at hall'
    simp only [cata_ty_tuple]
    refine h.tuple _ _ (by rw [List.length_map, List.length_map]; exact of_decide_eq_true hlen) ?_
    intro p q hpq
    rw [List.zip_map, List.mem_map] at hpq
    obtain ⟨⟨x, y⟩, hxy, hpq⟩ := hpq
    cases hpq
    exact ih (x, y) hxy (hall' (x, y) hxy)
  case case19 n1 xs n2 ys _ _ ih12 ih21 =>
    obtain ⟨hnl, hall⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨hn, hlen⟩ := Bool.and_eq_true_iff.mp hnl
    have hn' : n1 = n2 := of_decide_eq_true hn
    subst hn'
    have hall' : (xs.zipIdx.zip ys.zipIdx).all (fun pq : (Ty × Nat) × (Ty × Nat) =>
        (Ty.argVariance n1 pq.1.2).select (Ty.sub pq.1.1 pq.2.1) (Ty.sub pq.2.1 pq.1.1)) = true := by
      rw [← Ty.all_attach_eq]
      exact hall
    rw [List.all_eq_true] at hall'
    simp only [cata_ty_app]
    refine h.app _ _ _ (by rw [List.length_map, List.length_map]; exact of_decide_eq_true hlen) ?_
    intro p q hpq
    rw [List.zipIdx_map, List.zipIdx_map, List.zip_map, List.mem_map] at hpq
    obtain ⟨⟨⟨x, i⟩, ⟨y, j⟩⟩, hxy, hpq⟩ := hpq
    cases hpq
    have hsel := hall' ((x, i), (y, j)) hxy
    show (match Ty.argVariance n1 i with
      | .co => Adm.le (cata_ty alg x).2 (cata_ty alg y).2
      | .contra => Adm.le (cata_ty alg y).2 (cata_ty alg x).2
      | .inv => Adm.le (cata_ty alg x).2 (cata_ty alg y).2 ∧ Adm.le (cata_ty alg y).2 (cata_ty alg x).2)
    cases hv : Ty.argVariance n1 i with
    | co =>
      rw [hv] at hsel
      exact ih12 ((x, i), (y, j)) hxy hsel
    | contra =>
      rw [hv] at hsel
      exact ih21 ((x, i), (y, j)) hxy hsel
    | inv =>
      rw [hv] at hsel
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsel
      exact ⟨ih12 ((x, i), (y, j)) hxy h1, ih21 ((x, i), (y, j)) hxy h2⟩
  -- every other pair: `sub` answers `false`
  case case20 => exact Bool.noConfusion hsub

/-! ## The named, item and entry reads, monotone (decisions rows 125, 159, 165) -/

/-- **Monotonicity of the named read**: under one list of names, a field optional where it was
required (the flag implication) and a checker that admits more admit more. -/
theorem namedHasTy_mono :
    ∀ (cf cg : List (String × Bool × (Val → Bool))) (ns xs : List Val),
      cf.map Prod.fst = cg.map Prod.fst →
      (∀ p ∈ cf.zip cg, (p.1.2.1 = true → p.2.2.1 = true) ∧
        ∀ x, p.1.2.2 x = true → p.2.2.2 x = true) →
      namedHasTy cf ns xs = true → namedHasTy cg ns xs = true
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hh, _, _ => nomatch hh
  | _ :: _, [], _, _, hh, _, _ => nomatch hh
  | (n, o, c) :: cf, (m, p, d) :: cg, ns, xs, hh, hpt, h => by
    simp only [List.map_cons, List.cons.injEq] at hh
    obtain ⟨rfl, hrest⟩ := hh
    obtain ⟨hop, hc⟩ := hpt ((n, o, c), (n, p, d)) List.mem_cons_self
    have hpt' : ∀ q ∈ cf.zip cg, (q.1.2.1 = true → q.2.2.1 = true) ∧
        ∀ x, q.1.2.2 x = true → q.2.2.2 x = true :=
      fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    match ns, xs, h with
    | [], [], h =>
      simp only [namedHasTy, Bool.and_eq_true] at h ⊢
      exact ⟨hop h.1, namedHasTy_mono cf cg [] [] hrest hpt' h.2⟩
    | [], _ :: _, h => exact Bool.noConfusion h
    | v0 :: _, [], h => cases v0 <;> exact Bool.noConfusion h
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [namedHasTy] at h ⊢
        by_cases hk : k = n
        · rw [if_pos hk, Bool.and_eq_true] at h
          rw [if_pos hk, Bool.and_eq_true]
          exact ⟨hc x h.1, namedHasTy_mono cf cg ns xs hrest hpt' h.2⟩
        · rw [if_neg hk, Bool.and_eq_true] at h
          rw [if_neg hk, Bool.and_eq_true]
          exact ⟨hop h.1, namedHasTy_mono cf cg (.str k :: ns) (x :: xs) hrest hpt' h.2⟩
      | _ => exact Bool.noConfusion h

/-- Pointwise stronger checkers of one arity admit more (the tuple read). -/
theorem itemsHasTy_mono :
    ∀ (xs : List Val) (cs ds : List (Val → Bool)), cs.length = ds.length →
      (∀ p ∈ cs.zip ds, ∀ x, p.1 x = true → p.2 x = true) →
      itemsHasTy cs xs = true → itemsHasTy ds xs = true
  | [], [], [], _, _, _ => rfl
  | x :: xs, c :: cs, d :: ds, hlen, hpt, h => by
    simp only [itemsHasTy, Bool.and_eq_true] at h ⊢
    exact ⟨hpt (c, d) List.mem_cons_self x h.1,
      itemsHasTy_mono xs cs ds (Nat.succ.inj hlen)
        (fun p hp => hpt p (List.mem_cons_of_mem _ hp)) h.2⟩
  | [], [], _ :: _, hlen, _, _ => nomatch hlen
  | [], _ :: _, _, _, _, h => Bool.noConfusion h
  | _ :: _, [], _, _, _, h => Bool.noConfusion h
  | _ :: _, _ :: _, [], hlen, _, _ => nomatch hlen

/-- Stronger key and value checks admit more entries (the map read). -/
theorem entriesHasTy_mono {ck cv ck' cv' : Val → Bool} (hk : ∀ a, ck a = true → ck' a = true)
    (hv : ∀ x, cv x = true → cv' x = true) (es : List Val)
    (h : entriesHasTy ck cv es = true) : entriesHasTy ck' cv' es = true := by
  unfold entriesHasTy at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun e he => ?_⟩
  have := h.2 e he
  cases e
  case pair a x =>
    simp only [Bool.and_eq_true] at this ⊢
    exact ⟨hk a this.1, hv x this.2⟩
  all_goals exact this

/-- A field's checker read off an admission carrier at an allocation table. -/
def admChecker (al : List String) (c : Bool × Ty × Adm) : Bool × (Val → Bool) :=
  (c.1, fun y => c.2.2 y al)

/-- The membership algebra's field companion is a payload map. -/
theorem fieldCheckers_foldr (ps : List (String × Bool × Ty × Adm)) (al : List String) :
    List.foldr
      (fun x rrest allocated => (x.fst, x.snd.fst, fun y => x.snd.snd.snd y allocated) :: rrest allocated)
      (fun _ => []) ps al = ps.map (fun q => (q.1, admChecker al q.2)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih]
    rfl

/-- The membership algebra's item companion is a map. -/
theorem itemCheckers_foldr (ps : List (Ty × Adm)) (al : List String) :
    List.foldr (fun r rrest allocated => (fun x => r.snd x allocated) :: rrest allocated)
      (fun _ => []) ps al = ps.map (fun r x => r.2 x al) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih]

/-- Equal heads (names and flags) in one order, and every checker of the first below its partner's:
the named read admits more. -/
theorem namedHasTy_of_pairs (al : List String) {cf cg : List (String × Bool × Ty × Adm)}
    (hh : cf.map (fun p => (p.1, p.2.1)) = cg.map (fun p => (p.1, p.2.1)))
    (hpt : ∀ p q, (p, q) ∈ cf.zip cg → Adm.le p.2.2.2 q.2.2.2) (ns xs : List Val)
    (h : namedHasTy (cf.map (fun q => (q.1, admChecker al q.2))) ns xs = true) :
    namedHasTy (cg.map (fun q => (q.1, admChecker al q.2))) ns xs = true := by
  refine namedHasTy_mono _ _ ns xs ?_ ?_ h
  · have hn := congrArg (List.map Prod.fst) hh
    simp only [List.map_map, Function.comp_def] at hn ⊢
    exact hn
  · intro pq hpq
    rw [List.zip_map, List.mem_map] at hpq
    obtain ⟨⟨p, q⟩, hpq', rfl⟩ := hpq
    have hflag : p.2.1 = q.2.1 := Ty.zip_flag hh hpq'
    refine ⟨fun hf => ?_, fun x hx => hpt p q hpq' x al hx⟩
    show q.2.1 = true
    rw [← hflag]
    exact hf

/-! ## The condition discharged for the admission fold of this tree

Fourteen fields, one per constructor. Six are `rfl` because the arm is a constant or reads only
its own results (`never`, `union`, `top`, `var`) or ignores its argument outright — the two
invariant handles, which is decisions row 44 (a handle is coarse by kind; the world's tables
type what it holds) stated as a law rather than left as a comment. `fiberOf` is the identity
for the same reason. The seven that inspect the value are the hand definition's own arms: the
same `dsimp only [...]` then `split at hv` that proves `Val.hasTy`'s laws, because the emitted
arm carries the matcher `Val.hasTy` wrote (`FoldOf.lean`'s `matchOnCtorDiscr`).

The whole instance depends on `[propext]` alone. -/

theorem Val.hasTy_admitsSub : AdmitsSub Val.hasTy.alg where
  never := fun _ _ => rfl
  union := fun _ _ _ _ => rfl
  top := fun _ _ => rfl
  var := fun _ _ _ => rfl
  lit_string := by
    intro s v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · exact Bool.noConfusion hv
  option := by
    intro p0 q0 h v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · rename_i w
      exact h w al hv
    · exact Bool.noConfusion hv
  list := by
    intro p0 q0 h v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact list_all_mono _ (fun id => h (Val.fiber id) al) hv
      · exact Bool.noConfusion hv
    · rename_i vs
      exact list_all_mono vs (fun w => h w al) hv
    · exact Bool.noConfusion hv
  prod := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i x y
      simp only [Bool.and_eq_true_iff] at hv ⊢
      exact ⟨h0 x al hv.1, h1 y al hv.2⟩
    · exact Bool.noConfusion hv
  except := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ al hv
    · exact h1 _ al hv
    · exact Bool.noConfusion hv
  exitOf := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ al hv
    · split at hv
      · exact causeAdmits_mono_sub (fun w hw => h1 w al hw) _ hv
      · exact Bool.noConfusion hv
    · exact Bool.noConfusion hv
  causeOf := by
    intro p0 q0 h v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact causeAdmits_mono_sub (fun w hw => h w al hw) _ hv
    · exact Bool.noConfusion hv
  fiberOf := fun _ _ _ _ _ _ => Adm.le_refl _
  refOf := fun _ _ _ => Adm.le_refl _
  deferredOf := fun _ _ _ _ _ _ => Adm.le_refl _
  nat_int := by
    intro v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · exact Bool.noConfusion hv
  int_number := by
    intro v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    unfold numberImage
    rw [hv]
    rfl
  undefined_unit := fun _ _ hv => hv
  record := by
    intro ps qs hh hpt v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i ns xs _
      rw [fieldCheckers_foldr, Ty.canon, Field.canonBy_map] at hv ⊢
      exact namedHasTy_of_pairs al hh hpt ns xs hv
    · exact Bool.noConfusion hv
  map := by
    intro p0 p1 q0 q1 hk hv0 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact entriesHasTy_mono (fun a => hk.1 a al) (fun x => hv0 x al) _ hv
    · exact Bool.noConfusion hv
  tuple := by
    intro ps qs hlen hpt v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i xs
      rw [itemCheckers_foldr] at hv ⊢
      refine itemsHasTy_mono xs _ _ (by rw [List.length_map, List.length_map, hlen]) ?_ hv
      intro pq hpq x hx
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨p, q⟩, hpq', rfl⟩ := hpq
      exact hpt p q hpq' x al hx
    · exact Bool.noConfusion hv
  -- a nominal reference reads only its name (decisions row 158): the arm ignores its arguments
  app := fun _ _ _ _ _ => Adm.le_refl _

/-- **The monotone condition discharged for the admission fold of this tree**: membership reads
every position forward at the value level (a handle ignores its argument), which is what
instantiating a template at wider bindings needs (`Template.lean`, `cata_admits_instantiate`). -/
theorem Val.hasTy_admitsMono : AdmitsMono Val.hasTy.alg where
  option := Val.hasTy_admitsSub.option
  list := Val.hasTy_admitsSub.list
  prod := Val.hasTy_admitsSub.prod
  except := Val.hasTy_admitsSub.except
  exitOf := Val.hasTy_admitsSub.exitOf
  causeOf := Val.hasTy_admitsSub.causeOf
  fiberOf := Val.hasTy_admitsSub.fiberOf
  union := by
    intro p0 p1 q0 q1 h0 h1 v al hv
    simp only [Val.hasTy_admitsSub.union] at hv ⊢
    exact (Bool.or_eq_true_iff.mp hv).elim (fun h => Bool.or_eq_true_iff.mpr (Or.inl (h0 v al h)))
      (fun h => Bool.or_eq_true_iff.mpr (Or.inr (h1 v al h)))
  refOf := fun _ _ _ => Adm.le_refl _
  deferredOf := fun _ _ _ _ _ _ => Adm.le_refl _
  record := by
    intro ps qs hh hpt v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i ns xs _
      rw [fieldCheckers_foldr] at hv ⊢
      -- one paired list, its two projections: the canonical order reads names only, so both
      -- sides select the same positions (first occurrence kept)
      have hzip : ∀ (l1 l2 : List (String × Bool × Ty × Adm)),
          l1.map (fun p => (p.1, p.2.1)) = l2.map (fun p => (p.1, p.2.1)) →
          (∀ p q, (p, q) ∈ l1.zip l2 → Adm.le p.2.2.2 q.2.2.2) →
          ∃ zs : List (String × (Bool × Ty × Adm) × (Bool × Ty × Adm)),
            l1 = zs.map (fun z => (z.1, z.2.1)) ∧ l2 = zs.map (fun z => (z.1, z.2.2)) ∧
            ∀ z ∈ zs, z.2.1.1 = z.2.2.1 ∧ Adm.le z.2.1.2.2 z.2.2.2.2 := by
        intro l1
        induction l1 with
        | nil =>
          intro l2 hl _
          cases l2 with
          | nil => exact ⟨[], rfl, rfl, fun _ h => absurd h List.not_mem_nil⟩
          | cons _ _ => exact absurd hl (by simp only [List.map_nil, List.map_cons]; exact (List.cons_ne_nil _ _).symm)
        | cons a l1 ih =>
          intro l2 hl hp
          cases l2 with
          | nil => exact absurd hl (by simp only [List.map_nil, List.map_cons]; exact List.cons_ne_nil _ _)
          | cons b l2 =>
            simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hl
            obtain ⟨zs, h1, h2, hz⟩ := ih l2 hl.2 (fun p q h => hp p q (List.mem_cons_of_mem _ h))
            refine ⟨(a.1, a.2, b.2) :: zs, ?_, ?_, ?_⟩
            · rw [List.map_cons, ← h1]
            · rw [List.map_cons, ← h2, hl.1.1]
            · intro z hz'
              rcases List.mem_cons.mp hz' with rfl | hz'
              · exact ⟨hl.1.2, hp a b List.mem_cons_self⟩
              · exact hz z hz'
      obtain ⟨zs, h1, h2, hz⟩ := hzip ps qs hh hpt
      subst h1
      subst h2
      rw [List.map_map] at hv ⊢
      have hc1 := Field.canonBy_map (key := Field.bytesKey)
        (fun c : (Bool × Ty × Adm) × (Bool × Ty × Adm) => admChecker al c.1) zs
      have hc2 := Field.canonBy_map (key := Field.bytesKey)
        (fun c : (Bool × Ty × Adm) × (Bool × Ty × Adm) => admChecker al c.2) zs
      simp only [Function.comp_def] at hv ⊢
      rw [Ty.canon] at hv ⊢
      rw [hc1] at hv
      rw [hc2]
      refine namedHasTy_mono _ _ ns xs ?_ ?_ hv
      · simp only [List.map_map, Function.comp_def]
      · intro pq hpq
        rw [List.zip_map, List.mem_map] at hpq
        obtain ⟨⟨z1, z2⟩, hzz, rfl⟩ := hpq
        have heq : z1 = z2 := Ty.mem_zip_self hzz
        subst heq
        obtain ⟨hf, hle⟩ := hz z1 (Field.mem_canonBy (List.of_mem_zip hzz).1)
        refine ⟨fun h => ?_, fun x hx => hle x al hx⟩
        show z1.2.2.1 = true
        rw [← hf]
        exact h
    · exact Bool.noConfusion hv
  map := by
    intro p0 p1 q0 q1 hk hv0 v al hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact entriesHasTy_mono (fun a => hk a al) (fun x => hv0 x al) _ hv
    · exact Bool.noConfusion hv
  tuple := Val.hasTy_admitsSub.tuple
  app := fun _ _ _ _ _ => Adm.le_refl _

/-- The subtype relation on `Ty` respects value typing (`hasTy`). If `Ty.sub a b = true`
and value `v` has type `a`, then `v` also has type `b`.

There is no case analysis here at all: the two lines above it are the whole proof. The law is
`cata_admits_sub` — monotonicity along `sub` is a condition on the ALGEBRA — applied to
`Val.hasTy_admitsSub` through `Val.hasTy.eq_cata`, which is what makes a new constructor of
`Ty` cost one field in the instance rather than an arm in every proof that carries membership.
Statement and argument order are unchanged from the direct proof this replaces, so no call
site moved. -/
theorem hasTy_sub (a b : Ty) (v : Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true := by
  rw [Val.hasTy.eq_cata v a allocated] at hv
  rw [Val.hasTy.eq_cata v b allocated]
  exact cata_admits_sub Val.hasTy_admitsSub hsub v allocated hv

/-! ## Monotonicity in the allocation table -/

/-- An admission algebra whose twenty arms satisfy `AdmitsExtend` has a fold that preserves
extension of the allocation table. -/
theorem cata_admits_extend {alg : TyAlgebra AdmCarrier} (h : AdmitsExtend alg) (ty : Ty) :
    Adm.Extends (cata_ty alg ty).2 := by
  induction ty with
  | never => exact h.never
  | unit => exact h.unit
  | nat => exact h.nat
  | int => exact h.int
  | string => exact h.string
  | bool => exact h.bool
  | handle target => exact h.handle target
  | option _ ih => exact h.option _ ih
  | list _ ih => exact h.list _ ih
  | prod _ _ ih1 ih2 => exact h.prod _ _ ih1 ih2
  | except _ _ ih1 ih2 => exact h.except _ _ ih1 ih2
  | exitOf _ _ ih1 ih2 => exact h.exitOf _ _ ih1 ih2
  | causeOf _ ih => exact h.causeOf _ ih
  | fiberOf _ _ ih1 ih2 => exact h.fiberOf _ _ ih1 ih2
  | union _ _ ih1 ih2 => exact h.union _ _ ih1 ih2
  | lit value => exact h.lit value
  | refOf _ ih => exact h.refOf _ ih
  | deferredOf _ _ ih1 ih2 => exact h.deferredOf _ _ ih1 ih2
  | var index => exact h.var index
  | unknown => exact h.unknown
  | record fs ih =>
    rw [cata_ty_record]
    refine h.record _ fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq
  | map _ _ ih1 ih2 => exact h.map _ _ ih1 ih2
  | tuple ts ih =>
    rw [cata_ty_tuple]
    refine h.tuple _ fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq
  | app n ts ih =>
    rw [cata_ty_app]
    refine h.app n _ fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ih q hq
  | null => exact h.null
  | undefined => exact h.undefined
  | number => exact h.number
  | bytes => exact h.bytes

/-- The extension condition discharged for `Val.hasTy.alg`. -/
theorem Val.hasTy_admitsExtend : AdmitsExtend Val.hasTy.alg where
  never := fun _ _ _ _ hv => by
    dsimp only [Val.hasTy.alg] at hv
    exact Bool.noConfusion hv
  unit := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  nat := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  int := fun _ _ _ _ hv => hv
  string := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  bool := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  handle := by
    intro target v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact hv
      · exact hv
      · obtain ⟨ht, hi⟩ := Bool.and_eq_true_iff.mp hv
        simp only [ht]
        exact beq_iff_eq.mpr (ext _ target (beq_iff_eq.mp hi))
      · exact Bool.noConfusion hv
    · exact hv
  option := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rfl
    · rename_i w
      exact h0 w a b ext hv
    · exact Bool.noConfusion hv
  list := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact list_all_mono _ (fun id => h0 (Val.fiber id) a b ext) hv
      · exact Bool.noConfusion hv
    · rename_i vs
      exact list_all_mono vs (fun w => h0 w a b ext) hv
    · exact Bool.noConfusion hv
  prod := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i x y
      simp only [Bool.and_eq_true_iff] at hv ⊢
      exact ⟨h0 x a b ext hv.1, h1 y a b ext hv.2⟩
    · exact Bool.noConfusion hv
  except := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ a b ext hv
    · exact h1 _ a b ext hv
    · exact Bool.noConfusion hv
  exitOf := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact h0 _ a b ext hv
    · split at hv
      · exact causeAdmits_mono_sub (fun w hw => h1 w a b ext hw) _ hv
      · exact Bool.noConfusion hv
    · exact Bool.noConfusion hv
  causeOf := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact causeAdmits_mono_sub (fun w hw => h0 w a b ext hw) _ hv
    · exact Bool.noConfusion hv
  fiberOf := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  union := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    obtain h | h := Bool.or_eq_true_iff.mp hv
    · exact Bool.or_eq_true_iff.mpr (Or.inl (h0 v a b ext h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (h1 v a b ext h))
  lit := by
    intro s v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [exact hv; exact Bool.noConfusion hv]
  refOf := by
    intro p0 h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [exact hv; exact Bool.noConfusion hv]
  deferredOf := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [exact hv; exact Bool.noConfusion hv]
  var := fun _ _ _ _ _ hv => by
    dsimp only [Val.hasTy.alg] at hv
    exact Bool.noConfusion hv
  unknown := fun _ _ _ _ _ => rfl
  record := by
    intro ps h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i ns xs _
      rw [fieldCheckers_foldr, Ty.canon, Field.canonBy_map] at hv ⊢
      refine namedHasTy_mono _ _ ns xs (by simp only [List.map_map]; rfl) ?_ hv
      intro pq hpq
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨p, q⟩, hpq', rfl⟩ := hpq
      have heq : p = q := Ty.mem_zip_self hpq'
      subst heq
      exact ⟨id, fun x hx => h0 p (Field.mem_canonBy (List.of_mem_zip hpq').1) x a b ext hx⟩
    · exact Bool.noConfusion hv
  map := by
    intro p0 p1 h0 h1 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · exact entriesHasTy_mono (fun k => h0 k a b ext) (fun x => h1 x a b ext) _ hv
    · exact Bool.noConfusion hv
  tuple := by
    intro ps h0 v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · rename_i xs
      rw [itemCheckers_foldr] at hv ⊢
      refine itemsHasTy_mono xs _ _ (by rw [List.length_map, List.length_map]) ?_ hv
      intro pq hpq x hx
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨p, q⟩, hpq', rfl⟩ := hpq
      have heq : p = q := Ty.mem_zip_self hpq'
      subst heq
      exact h0 p (List.of_mem_zip hpq').1 x a b ext hx
    · exact Bool.noConfusion hv
  app := by
    intro n _ _ v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv
    · split at hv
      · exact hv
      · exact hv
      · obtain ⟨ht, hi⟩ := Bool.and_eq_true_iff.mp hv
        simp only [ht]
        exact beq_iff_eq.mpr (ext _ n (beq_iff_eq.mp hi))
      · exact Bool.noConfusion hv
    · exact hv
  null := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  undefined := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]
  number := fun _ _ _ _ hv => hv
  bytes := by
    intro v a b ext hv
    dsimp only [Val.hasTy.alg] at hv ⊢
    split at hv <;> [rfl; exact Bool.noConfusion hv]

/-- Membership is monotone in the allocation table at every type. -/
theorem hasTy_mono (ty : Ty) (v : Val) (a b : List String)
    (ext : Extends a b) (typed : Val.hasTy v ty a = true) : Val.hasTy v ty b = true := by
  rw [Val.hasTy.eq_cata v ty a] at typed
  rw [Val.hasTy.eq_cata v ty b]
  exact cata_admits_extend Val.hasTy_admitsExtend ty v a b ext typed

/-- In cause admission, discarding the type argument makes the choice of type irrelevant. -/
theorem causeAdmits_discard_ty (m : Val → Bool) (t1 t2 : Ty) (c : CauseV) :
    causeAdmits (fun w _ => m w) t1 c = causeAdmits (fun w _ => m w) t2 c := by
  apply List.all_congr rfl
  intro r
  cases r with
  | fail e _ => dsimp only [reasonAdmits]
  | die _ _ => rfl
  | interrupt _ _ => rfl

/-- What an admission algebra satisfies when its arms respect equality of admitted values.
The congruence arms preserve pointwise agreement of their subterm admissions; the coarse
handles ignore normalisation of their arguments. -/
structure AdmitsNormalize (alg : TyAlgebra AdmCarrier) : Prop where
  option : ∀ p0 q0, (p0).2 = (q0).2 → (alg.ty_option p0).2 = (alg.ty_option q0).2
  list : ∀ p0 q0, (p0).2 = (q0).2 → (alg.ty_list p0).2 = (alg.ty_list q0).2
  except : ∀ p0 p1 q0 q1, (p0).2 = (q0).2 → (p1).2 = (q1).2 → (alg.ty_except p0 p1).2 = (alg.ty_except q0 q1).2
  exitOf : ∀ p0 p1 q0 q1, (p0).2 = (q0).2 → (p1).2 = (q1).2 → (alg.ty_exitOf p0 p1).2 = (alg.ty_exitOf q0 q1).2
  causeOf : ∀ p0 q0, (p0).2 = (q0).2 → (alg.ty_causeOf p0).2 = (alg.ty_causeOf q0).2
  fiberOf : ∀ p0 p1 q0 q1, (alg.ty_fiberOf p0 p1).2 = (alg.ty_fiberOf q0 q1).2
  refOf : ∀ p0 q0, (alg.ty_refOf p0).2 = (alg.ty_refOf q0).2
  deferredOf : ∀ p0 p1 q0 q1, (alg.ty_deferredOf p0 p1).2 = (alg.ty_deferredOf q0 q1).2

/-- The congruence condition for normalisation discharged for `Val.hasTy.alg`. -/
theorem Val.hasTy_admitsNormalize : AdmitsNormalize Val.hasTy.alg where
  option := fun _ _ h => by dsimp only [Val.hasTy.alg]; rw [h]
  list := fun _ _ h => by dsimp only [Val.hasTy.alg]; rw [h]
  except := fun _ _ _ _ h0 h1 => by dsimp only [Val.hasTy.alg]; rw [h0, h1]
  exitOf := by
    intro p0 p1 q0 q1 h0 h1
    dsimp only [Val.hasTy.alg]
    rw [h0, h1]
    funext v allocated
    split
    · rfl
    · split
      · exact causeAdmits_discard_ty (fun w => q1.snd w allocated) p1.fst q1.fst _
      · rfl
    · rfl
  causeOf := by
    intro p0 q0 h
    dsimp only [Val.hasTy.alg]
    rw [h]
    funext v allocated
    split
    · exact causeAdmits_discard_ty (fun w => q0.snd w allocated) p0.fst q0.fst _
    · rfl
  fiberOf := fun _ _ _ _ => rfl
  refOf := fun _ _ => rfl
  deferredOf := fun _ _ _ _ => rfl

end Effect4.Program
