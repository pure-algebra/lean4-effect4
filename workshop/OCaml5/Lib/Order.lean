/-!
# `OCaml5.Lib.Order` — the comparator

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§4.2 ("every library construct whose behaviour we claim has a Lean carrier with laws").
Report: `docs/research/2026-09-04-seat-w4-library-carriers.md`.

## What this stands for

`Base.Comparator.S`: an OCaml `Map`/`Set` is indexed by a **comparator witness**, a first-class
module carrying `compare : 'a -> 'a -> int` and a `sexp_of_t`, together with the *unstated but
relied-on* promise that `compare` is a total order. `Base.Map.M(K).t` is a map whose keys are
ordered by `K.comparator`. `LinOrd` is that promise made into a class: the comparator plus the
four laws every `Base.Map` lemma in this file needs.

`Ordering` stands for the sign of `compare`: `Base` returns an `int` and only its sign is
specified (`Base.Comparable` doc: "the result is negative / zero / positive"). Modelling the sign
rather than the `int` is deliberate — nothing we rely on can observe the magnitude, and a
carrier that could would be claiming more than `Base` promises.

## Named properties (theorem names are stable; cite these)

* `LinOrd.cmp_self` — `compare x x = 0`.
* `LinOrd.eq_of_cmp_eq` — `compare x y = 0 → x = y` (antisymmetry, the half `Base` needs to make
  a `Map` key unique).
* `LinOrd.cmp_swap` — `compare y x` is the sign flip of `compare x y`.
* `LinOrd.cmp_trans_lt` — `<` is transitive.
* `LinOrd.cmp_eq_iff` — `compare x y = 0 ↔ x = y`.
* `LinOrd.cmp_total` — every pair is `lt`, `eq` or `gt` (`Ordering` has no fourth case, so this
  is a case analysis, recorded because "total" is what the name `LinOrd` claims).
* `LinOrd.gt_of_lt`, `LinOrd.lt_asymm`, `LinOrd.lt_irrefl` — the one-line consequences.

## Refusals

* **`compare` as an `int`.** `Base` hands back an `int`; only its sign is specified. A carrier
  over `Int` would let a caller depend on the magnitude, which `Base` does not promise. Refusal
  row `W4-ORD-INT-MAGNITUDE`.
* **Physical-equality shortcuts.** `Base`'s `compare` on some types tests `phys_equal` first.
  That is invisible through the sign and is not modelled. Refusal row `W4-ORD-PHYS-EQUAL`.
* **`Comparator.Poly` / polymorphic compare.** `Base.Poly.compare` is `Stdlib.compare`, which is
  the "no magic" prohibition of the plan §4.4. There is no instance for it here and there never
  should be. Refusal row `W4-ORD-POLY-COMPARE`.
-/

namespace OCaml5.Lib

universe u v

/-- A decidable total order, in the shape `Base.Comparator.S` promises: one `compare` whose sign
is `Ordering`, with the four laws every `Map`/`Set` fact below rests on. -/
class LinOrd (α : Type u) where
  /-- `Base`'s `compare`, as its sign. -/
  cmp : α → α → Ordering
  /-- `compare x x = 0`. -/
  cmp_self : ∀ a : α, cmp a a = .eq
  /-- Antisymmetry: keys that compare equal *are* equal, which is what makes a `Map` key
  unique. -/
  eq_of_cmp_eq : ∀ {a b : α}, cmp a b = .eq → a = b
  /-- `compare y x` is the sign flip of `compare x y`. -/
  cmp_swap : ∀ a b : α, cmp b a = (cmp a b).swap
  /-- `<` is transitive. -/
  cmp_trans_lt : ∀ {a b c : α}, cmp a b = .lt → cmp b c = .lt → cmp a c = .lt

namespace LinOrd

variable {α : Type u} [LinOrd α]

/-- `compare x y = 0 ↔ x = y`. -/
theorem cmp_eq_iff {a b : α} : cmp a b = .eq ↔ a = b := by
  constructor
  · exact eq_of_cmp_eq
  · rintro rfl; exact cmp_self a

/-- Every pair is `lt`, `eq` or `gt`: `Ordering` has no fourth case. -/
theorem cmp_total (a b : α) : cmp a b = .lt ∨ cmp a b = .eq ∨ cmp a b = .gt := by
  cases cmp a b <;> simp

/-- `x < y` forces `y > x`. -/
theorem gt_of_lt {a b : α} (h : cmp a b = .lt) : cmp b a = .gt := by
  rw [cmp_swap, h]; rfl

/-- Nothing is below itself. -/
theorem lt_irrefl (a : α) : cmp a a ≠ .lt := by
  rw [cmp_self]; intro h; cases h

/-- `<` is asymmetric. -/
theorem lt_asymm {a b : α} (h : cmp a b = .lt) : cmp b a ≠ .lt := by
  rw [gt_of_lt h]; intro h'; cases h'

/-- Two distinct keys compare `lt` one way or the other. -/
theorem lt_or_gt_of_ne {a b : α} (h : a ≠ b) : cmp a b = .lt ∨ cmp a b = .gt := by
  rcases cmp_total a b with h' | h' | h'
  · exact Or.inl h'
  · exact absurd (eq_of_cmp_eq h') h
  · exact Or.inr h'

/-- The decision procedure a comparator carries. Not an instance: a type may already have a
`DecidableEq` and two would fight. -/
def decEq (a b : α) : Decidable (a = b) :=
  if h : cmp a b = .eq then .isTrue (eq_of_cmp_eq h)
  else .isFalse fun he => h (he ▸ cmp_self a)

/-- Transport a comparator along an injection. This is `Base.Comparator.Make` over a
`Comparable.S` obtained by `comparing f`. -/
@[instance_reducible] def onKey {β : Type v} [LinOrd β] (f : α → β) (hf : ∀ {a b : α}, f a = f b → a = b) :
    LinOrd α where
  cmp a b := cmp (f a) (f b)
  cmp_self a := cmp_self (f a)
  eq_of_cmp_eq h := hf (eq_of_cmp_eq h)
  cmp_swap a b := cmp_swap (f a) (f b)
  cmp_trans_lt h₁ h₂ := cmp_trans_lt h₁ h₂

end LinOrd

/-! ## `Base.Int.comparator` -/

/-- `Base.Int.compare` as its sign. -/
def natCmp (a b : Nat) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

theorem natCmp_lt_iff {a b : Nat} : natCmp a b = .lt ↔ a < b := by
  unfold natCmp
  by_cases h₁ : a < b
  · simp [h₁]
  · by_cases h₂ : b < a <;> simp [h₁, h₂]

theorem natCmp_eq_iff {a b : Nat} : natCmp a b = .eq ↔ a = b := by
  unfold natCmp
  by_cases h₁ : a < b
  · simp [h₁]; omega
  · by_cases h₂ : b < a <;> simp [h₁, h₂] <;> omega

theorem natCmp_gt_iff {a b : Nat} : natCmp a b = .gt ↔ b < a := by
  unfold natCmp
  by_cases h₁ : a < b
  · simp [h₁]; omega
  · by_cases h₂ : b < a <;> simp [h₁, h₂]

instance : LinOrd Nat where
  cmp := natCmp
  cmp_self a := natCmp_eq_iff.mpr rfl
  eq_of_cmp_eq h := natCmp_eq_iff.mp h
  cmp_swap a b := by
    unfold natCmp
    by_cases h₁ : a < b <;> by_cases h₂ : b < a <;> simp [h₁, h₂] <;> omega
  cmp_trans_lt h₁ h₂ :=
    natCmp_lt_iff.mpr (Nat.lt_trans (natCmp_lt_iff.mp h₁) (natCmp_lt_iff.mp h₂))

/-- The `Nat` comparator is `natCmp` on the nose. -/
theorem cmp_nat (a b : Nat) : LinOrd.cmp a b = natCmp a b := rfl

/-! ## `Base.Char.comparator` -/

instance : LinOrd Char :=
  LinOrd.onKey Char.toNat (fun {_ _} h => Char.ext (UInt32.toNat_inj.mp h))

/-! ## `Base.List.comparator`: lexicographic

`Base.List.compare` compares element by element and, on a common prefix, by length
(`base/src/list.ml`, the `[@@deriving compare]` on `'a list`). -/

/-- `Base`'s `Comparable.lexicographic` step: the first non-zero sign wins. -/
def ordThen : Ordering → Ordering → Ordering
  | .eq, o => o
  | .lt, _ => .lt
  | .gt, _ => .gt

@[simp] theorem ordThen_eq (o : Ordering) : ordThen .eq o = o := rfl
@[simp] theorem ordThen_lt (o : Ordering) : ordThen .lt o = .lt := rfl
@[simp] theorem ordThen_gt (o : Ordering) : ordThen .gt o = .gt := rfl

/-- Lexicographic comparison, `Base.List.compare`. -/
def listCmp {α : Type u} [LinOrd α] : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => ordThen (LinOrd.cmp a b) (listCmp as bs)

theorem listCmp_self {α : Type u} [LinOrd α] (l : List α) : listCmp l l = .eq := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [listCmp, LinOrd.cmp_self, ih]

theorem listCmp_eq {α : Type u} [LinOrd α] :
    ∀ {l₁ l₂ : List α}, listCmp l₁ l₂ = .eq → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [listCmp] at h
  | _ :: _, [], h => by simp [listCmp] at h
  | a :: as, b :: bs, h => by
    simp only [listCmp] at h
    cases hab : LinOrd.cmp a b with
    | lt => rw [hab] at h; simp at h
    | gt => rw [hab] at h; simp at h
    | eq =>
      rw [hab, ordThen_eq] at h
      rw [LinOrd.eq_of_cmp_eq hab, listCmp_eq h]

theorem listCmp_swap {α : Type u} [LinOrd α] :
    ∀ l₁ l₂ : List α, listCmp l₂ l₁ = (listCmp l₁ l₂).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp only [listCmp]
    rw [LinOrd.cmp_swap a b, listCmp_swap as bs]
    generalize LinOrd.cmp a b = o
    generalize listCmp as bs = p
    cases o <;> rfl

theorem listCmp_trans_lt {α : Type u} [LinOrd α] :
    ∀ {l₁ l₂ l₃ : List α}, listCmp l₁ l₂ = .lt → listCmp l₂ l₃ = .lt → listCmp l₁ l₃ = .lt
  | [], [], _, h, _ => by simp [listCmp] at h
  | [], _ :: _, [], _, h => by simp [listCmp] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [listCmp] at h
  | _ :: _, _ :: _, [], _, h => by simp [listCmp] at h
  | a :: as, b :: bs, c :: cs, h₁, h₂ => by
    simp only [listCmp] at h₁ h₂ ⊢
    rcases LinOrd.cmp_total a b with hab | hab | hab
    · rcases LinOrd.cmp_total b c with hbc | hbc | hbc
      · rw [LinOrd.cmp_trans_lt hab hbc, ordThen_lt]
      · rw [LinOrd.eq_of_cmp_eq hbc] at hab; rw [hab, ordThen_lt]
      · rw [hbc, ordThen_gt] at h₂; exact absurd h₂ (by simp)
    · have hb : a = b := LinOrd.eq_of_cmp_eq hab
      subst hb
      rw [LinOrd.cmp_self, ordThen_eq] at h₁
      rcases LinOrd.cmp_total a c with hac | hac | hac
      · rw [hac, ordThen_lt]
      · rw [hac, ordThen_eq] at h₂ ⊢
        exact listCmp_trans_lt h₁ h₂
      · rw [hac, ordThen_gt] at h₂; exact absurd h₂ (by simp)
    · rw [hab, ordThen_gt] at h₁; exact absurd h₁ (by simp)

instance {α : Type u} [LinOrd α] : LinOrd (List α) where
  cmp := listCmp
  cmp_self := listCmp_self
  eq_of_cmp_eq := listCmp_eq
  cmp_swap := listCmp_swap
  cmp_trans_lt := listCmp_trans_lt

/-! ## `Base.String.comparator` -/

instance : LinOrd String :=
  LinOrd.onKey String.toList (fun {_ _} h => String.ext h)

end OCaml5.Lib
