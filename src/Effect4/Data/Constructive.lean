module

/-!
# Effect4.Data.Constructive — Choice-free standard library foundation

This module collects verified constructive lemmas for core Lean datatypes (`Option`, `List`,
`Bool`, `Decidable`). Every declaration in this module is proved without `Classical.choice`,
strictly satisfying the repository's axiom ceiling (`[propext, Quot.sound]`).

Standard library lemmas (and Mathlib) frequently rely on classical choice for seemingly simple
identities (e.g. `Option.bind_eq_some` or `List.mem_iff`). Using this module guarantees that
reasoning over optional fields, associative lookup lists, and decidable predicates will never
silently pull in `Classical.choice` and fail the library axiom audit.

The list facts that the law graph proved in place are here too, each with its statement and its
proof as it was: zips, lookups and `flatMap` for the type templates
(`src/Effect4/Laws/Program/Template.lean`), and folds, `dropWhile`, `find?` and `erase` for the
passes of the composed modules (`src/Effect4/Laws/Modules/`). A fact here names lists, numbers
and names only. A fact that names a term, a type of the program or an atom stays in the law
graph.
-/

@[expose] public section

namespace Effect4.Constructive

universe u v w

/-! ## Option lemmas -/

namespace Option

/-- Constructive characterization of `Option.bind` returning `some`. -/
theorem bind_eq_some_iff {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) (b : β) :
    o.bind f = some b ↔ ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none =>
    simp only [Option.bind]
    constructor
    · intro h; contradiction
    · intro ⟨a, ha, _⟩; contradiction
  | some a =>
    simp only [Option.bind]
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · intro ⟨a', ha, hf⟩; cases ha; exact hf

/-- Constructive characterization of `Option.map` returning `some`. -/
theorem map_eq_some_iff {α : Type u} {β : Type v} (f : α → β) (o : Option α) (b : β) :
    o.map f = some b ↔ ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none =>
    simp only [Option.map]
    constructor
    · intro h; contradiction
    · intro ⟨a, ha, _⟩; contradiction
  | some a =>
    simp only [Option.map]
    constructor
    · intro h; injection h with h; exact ⟨a, rfl, h⟩
    · intro ⟨a', ha, hf⟩; cases ha; subst hf; rfl

/-- Constructive characterization of `Option.bind` returning `none`. -/
theorem bind_eq_none_iff {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) :
    o.bind f = none ↔ o = none ∨ ∃ a, o = some a ∧ f a = none := by
  cases o with
  | none =>
    constructor
    · intro _; left; rfl
    · intro _; rfl
  | some a =>
    simp only [Option.bind]
    constructor
    · intro h; right; exact ⟨a, rfl, h⟩
    · intro h; rcases h with h1 | ⟨a', ha, h2⟩
      · contradiction
      · cases ha; exact h2

/-- Constructive equivalence for `isSome`. -/
theorem isSome_iff_exists {α : Type u} (o : Option α) :
    o.isSome = true ↔ ∃ a, o = some a := by
  cases o with
  | none =>
    constructor
    · intro h; contradiction
    · intro ⟨a, ha⟩; contradiction
  | some a =>
    constructor
    · intro _; exact ⟨a, rfl⟩
    · intro _; rfl

/-- Constructive equivalence for `isNone`. -/
theorem isNone_iff_eq_none {α : Type u} (o : Option α) :
    o.isNone = true ↔ o = none := by
  cases o with
  | none =>
    constructor
    · intro _; rfl
    · intro _; rfl
  | some a =>
    constructor
    · intro h; contradiction
    · intro h; contradiction

end Option

/-! ## Bool and Decidable lemmas -/

namespace Bool

/-- Constructive reflection for boolean `and`. -/
theorem and_eq_true_iff (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

/-- Constructive reflection for boolean `or`. -/
theorem or_eq_true_iff (a b : Bool) :
    (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

/-- Constructive reflection for boolean `not`. -/
theorem not_eq_true_iff (a : Bool) :
    (!a) = true ↔ a = false := by
  cases a <;> simp

end Bool

namespace Decidable

/-- Reflecting decidable conjunction without classical excluded middle. -/
theorem decide_and {p q : Prop} [Decidable p] [Decidable q] :
    decide (p ∧ q) = true ↔ decide p = true ∧ decide q = true := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Reflecting decidable disjunction without classical excluded middle. -/
theorem decide_or {p q : Prop} [Decidable p] [Decidable q] :
    decide (p ∨ q) = true ↔ decide p = true ∨ decide q = true := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- Reflection of `decide p = true` to `p`. -/
theorem decide_iff {p : Prop} [Decidable p] :
    decide p = true ↔ p := by
  exact decide_eq_true_iff

/-- A number is not below another exactly when the other is at most it: the test that a step
writes with `not` and `lt`. -/
theorem not_decide_lt (a b : Nat) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases below : a < b
  · rw [decide_eq_true below, decide_eq_false (Nat.not_le_of_lt below)]
    rfl
  · rw [decide_eq_false below, decide_eq_true (Nat.le_of_not_lt below)]
    rfl

end Decidable

/-! ## List lemmas -/

namespace List

/-- Constructive characterization of `List.all` returning `true`. -/
theorem all_eq_true_iff {α : Type u} (p : α → Bool) (xs : List α) :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; contradiction
    · intro _; rfl
  | cons x xs ih =>
    simp only [List.all, Bool.and_eq_true_iff]
    constructor
    · intro ⟨hx, hxs⟩ y hy
      cases hy with
      | head => exact hx
      | tail _ htail => exact ih.mp hxs y htail
    · intro h
      constructor
      · exact h x (List.Mem.head xs)
      · apply ih.mpr
        intro y hy
        exact h y (List.Mem.tail x hy)

/-- Constructive characterization of `List.any` returning `true`. -/
theorem any_eq_true_iff {α : Type u} (p : α → Bool) (xs : List α) :
    xs.any p = true ↔ ∃ x ∈ xs, p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h; contradiction
    · intro ⟨x, hx, _⟩; contradiction
  | cons x xs ih =>
    simp only [List.any, Bool.or_eq_true_iff]
    constructor
    · intro h
      rcases h with hx | hxs
      · exact ⟨x, List.Mem.head xs, hx⟩
      · obtain ⟨y, hy, hpy⟩ := ih.mp hxs
        exact ⟨y, List.Mem.tail x hy, hpy⟩
    · intro ⟨y, hy, hpy⟩
      cases hy with
      | head => left; exact hpy
      | tail _ htail => right; exact ih.mpr ⟨y, htail, hpy⟩

/-- Constructive characterization of `List.find?` returning `some`. -/
theorem find?_eq_some_iff {α : Type u} (p : α → Bool) (xs : List α) (a : α) :
    xs.find? p = some a → a ∈ xs ∧ p a = true := by
  induction xs with
  | nil =>
    intro h
    contradiction
  | cons x xs ih =>
    intro h
    simp only [List.find?] at h
    split at h
    · next hp =>
      injection h with h
      subst h
      exact ⟨List.Mem.head xs, hp⟩
    · next _ =>
      have ⟨hin, hp_a⟩ := ih h
      exact ⟨List.Mem.tail x hin, hp_a⟩

/-- Constructive characterization of `List.lookup` on associative lists. -/
theorem lookup_mem {α : Type u} {β : Type v} [DecidableEq α]
    (xs : List (α × β)) (k : α) (v : β) :
    xs.lookup k = some v → (k, v) ∈ xs := by
  induction xs with
  | nil =>
    intro h
    contradiction
  | cons head tail ih =>
    intro h
    simp only [List.lookup] at h
    split at h
    · next heq =>
      injection h with h
      have heqk : k = head.1 := of_decide_eq_true heq
      subst heqk h
      cases head
      exact List.Mem.head tail
    · next _ =>
      have htail := ih h
      exact List.Mem.tail head htail

/-! ### Zips, lookups and `flatMap`

Steps of the claim `template-match-complete` (`src/Effect4/Laws/Program/Template.lean`,
`src/Effect4/Laws/Program/Bounds.lean`). -/

/-- `flatMap` respects pointwise equality on the list. It is a step of
`template-match-complete`, and `Bounds.cands_args` and `paramOccurrences_firsts` read it. -/
theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_congr_left h]

/-- A list zipped with its own image pairs each element with its image. It is a step of
`template-match-complete`, and `args_zip_of_map` reads it. -/
theorem mem_zip_map_self {α β : Type} {f : α → β} :
    ∀ {l : List α} {p : α × β}, p ∈ l.zip (l.map f) → p.2 = f p.1
  | [], _, hp => absurd hp List.not_mem_nil
  | a :: l, p, hp => by
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact mem_zip_map_self hp

/-- Of three aligned lists, a pair of the first two has a partner in the third at its position. It is a step of
`template-match-complete`, and `Bounds.below_args` and `Bounds.matchArgsB_monotone` read it. -/
theorem mem_zip_middle {α β γ : Type} : ∀ {xs : List α} {ys : List β} {zs : List γ},
    xs.length = zs.length → ys.length = zs.length → ∀ {a : α} {b : β}, (a, b) ∈ xs.zip ys →
      ∃ c, (a, c) ∈ xs.zip zs ∧ (b, c) ∈ ys.zip zs
  | [], _, _, _, _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, [], _, _, _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, _ :: _, [], hx, _, _, _, _ =>
    absurd hx (List.cons_ne_nil _ _ ∘ List.eq_nil_of_length_eq_zero)
  | x :: xs, y :: ys, z :: zs, hx, hy, a, b, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨z, List.mem_cons_self, List.mem_cons_self⟩
    · obtain ⟨c, hac, hbc⟩ := mem_zip_middle (Nat.succ.inj hx) (Nat.succ.inj hy) h
      exact ⟨c, List.mem_cons_of_mem _ hac, List.mem_cons_of_mem _ hbc⟩

/-- Two lists with one image pair elements of one image. It is a step of
`template-match-complete`, and `Bounds.above_args`, `Bounds.below_args` and `Bounds.cands_args` read it. -/
theorem eq_of_mem_zip_map {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {xs : List α} {ys : List β}, xs.map f = ys.map g → ∀ {a : α} {b : β},
      (a, b) ∈ xs.zip ys → f a = g b
  | [], _, _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, [], _, _, _, h => absurd h List.not_mem_nil
  | x :: xs, y :: ys, he, a, b, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at he
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact he.1
    · exact eq_of_mem_zip_map he.2 h

/-- A lookup in a list of distinct names finds the entry of that name. It is a step of
`template-match-complete`, and `Bounds.cands_args` reads it. -/
theorem lookup_of_mem_nodup {β : Type} :
    ∀ {L : List (String × β)}, (L.map Prod.fst).Nodup → ∀ {p : String × β}, p ∈ L →
      L.lookup p.1 = some p.2
  | [], _, _, hp => absurd hp List.not_mem_nil
  | q :: L, hnd, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [beq_iff_eq.mpr rfl]
    · have hne : p.1 ≠ q.1 := fun he => hnd.1 (he ▸ List.mem_map_of_mem hp)
      rw [beq_eq_false_iff_ne.mpr hne]
      exact lookup_of_mem_nodup hnd.2 hp

/-! ### Folds that build a list

Each says what a fold of a composed module's pass computes
(`src/Effect4/Laws/Modules/Queue/`, `src/Effect4/Laws/Modules/Semaphore/`). -/

/-- A fold that appends the elements it keeps is a filter. -/
theorem foldl_keep {α : Type} (p : α → Prop) [DecidablePred p] :
    ∀ (xs kept : List α),
      xs.foldl (fun kept x => if p x then kept else kept ++ [x]) kept =
        kept ++ xs.filter (fun x => !decide (p x))
  | [], kept => by rw [List.foldl_nil, List.filter_nil, List.append_nil]
  | x :: xs, kept => by
    rw [List.foldl_cons, foldl_keep p xs, List.filter_cons]
    by_cases holds : p x
    · rw [if_pos holds, decide_eq_true holds]
      rfl
    · rw [if_neg holds, decide_eq_false holds, List.append_assoc]
      rfl

/-- A fold that appends what each element gives is the list with the elements' gifts. -/
theorem foldl_append_flatMap {α β : Type} (f : α → List β) :
    ∀ (xs : List α) (init : List β),
      xs.foldl (fun acc x => acc ++ f x) init = init ++ xs.flatMap f
  | [], init => by rw [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | x :: xs, init => by
    rw [List.foldl_cons, foldl_append_flatMap f xs, List.flatMap_cons, List.append_assoc]

/-- A fold that appends one image of each element is the list with the images. -/
theorem foldl_snoc_map {α β : Type} (g : α → β) :
    ∀ (xs : List α) (init : List β),
      xs.foldl (fun out x => out ++ [g x]) init = init ++ xs.map g
  | [], init => by rw [List.foldl_nil, List.map_nil, List.append_nil]
  | x :: xs, init => by
    rw [List.foldl_cons, foldl_snoc_map g xs, List.map_cons, List.append_assoc]
    rfl

/-- A fold that keeps a flag is the flag, or any element's test. -/
theorem foldl_or_any {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (found : Bool), xs.foldl (fun found x => found || p x) found =
      (found || xs.any p)
  | [], found => by rw [List.foldl_nil, List.any_nil, Bool.or_false]
  | x :: xs, found => by
    rw [List.foldl_cons, foldl_or_any p xs, List.any_cons, Bool.or_assoc]

/-! ### The entries from the first one that satisfies a test

`List.erase_append` of core reaches `Classical.choice`, so the facts of `erase` below are proved
by induction on the list. -/

/-- A fold that keeps every entry from the first one that satisfies a test is `dropWhile`. With
entries already kept, it keeps every later entry. -/
theorem foldl_fromFirst {α : Type} (p : α → Bool) :
    ∀ (xs kept : List α),
      xs.foldl
          (fun kept x => if (!decide (kept.length = 0) || p x) = true then kept ++ [x] else kept)
          kept =
        if kept.length = 0 then xs.dropWhile (fun x => !p x) else kept ++ xs
  | [], kept => by
    rw [List.foldl_nil, List.dropWhile_nil, List.append_nil]
    by_cases empty : kept.length = 0
    · rw [if_pos empty]
      exact List.eq_nil_of_length_eq_zero empty
    · rw [if_neg empty]
  | x :: xs, kept => by
    rw [List.foldl_cons, foldl_fromFirst p xs]
    by_cases empty : kept.length = 0
    · have none : kept = [] := List.eq_nil_of_length_eq_zero empty
      subst none
      rw [List.dropWhile_cons]
      cases holds : p x with
      | true => rfl
      | false => rfl
    · have keeps : (!decide (kept.length = 0) || p x) = true := by
        rw [decide_eq_false empty]
        rfl
      have more : ¬ (kept ++ [x]).length = 0 := by
        rw [List.length_append]
        exact Nat.succ_ne_zero _
      rw [keeps, if_pos rfl, if_neg more, if_neg empty, List.append_assoc]
      rfl

/-- What `dropWhile` keeps is no longer than the list. -/
theorem length_dropWhile_le {α : Type} (q : α → Bool) :
    ∀ (xs : List α), (xs.dropWhile q).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    rw [List.dropWhile_cons]
    by_cases drops : q x = true
    · rw [if_pos drops]
      exact Nat.le_succ_of_le (length_dropWhile_le q xs)
    · rw [if_neg drops]
      exact Nat.le_refl _

/-- **The entries from the first one that satisfies a test, against `find?` and `erase`.** The
first kept entry is what `find?` answers. The entries before the kept ones, then the kept ones
without their first, are the list without that entry, or the whole list where no entry
satisfies the test. The removal compares no entry with another in the term: an earlier entry
that is equal to the found one would satisfy the test too, so `find?` would have answered
it. -/
theorem fromFirst_find? {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ (xs : List α),
      (xs.dropWhile (fun x => !p x))[0]? = xs.find? p ∧
        xs.take (xs.length - (xs.dropWhile (fun x => !p x)).length) ++
            (xs.dropWhile (fun x => !p x)).drop 1 =
          (match xs.find? p with
            | some w => xs.erase w
            | none => xs)
  | [] => ⟨rfl, rfl⟩
  | x :: xs => by
    obtain ⟨head, around⟩ := fromFirst_find? p xs
    rw [List.dropWhile_cons, List.find?_cons]
    cases holds : p x with
    | true =>
      rw [if_neg (by decide : ¬ ((!true) = true))]
      refine ⟨rfl, ?_⟩
      show (x :: xs).take ((x :: xs).length - (x :: xs).length) ++ xs = (x :: xs).erase x
      rw [Nat.sub_self, List.take_zero, List.nil_append, List.erase_cons,
        show (x == x) = true from decide_eq_true rfl, if_pos rfl]
    | false =>
      rw [if_pos (by decide : (!false) = true)]
      refine ⟨head, ?_⟩
      have shorter := length_dropWhile_le (fun x => !p x) xs
      have longer : (x :: xs).length - (xs.dropWhile (fun x => !p x)).length =
          (xs.length - (xs.dropWhile (fun x => !p x)).length) + 1 := by
        rw [List.length_cons]
        omega
      rw [longer, List.take_succ_cons, List.cons_append, around]
      cases found : xs.find? p with
      | none => rfl
      | some w =>
        have other : ¬ x = w := fun same => by
          have fitsW := List.find?_some found
          rw [← same, holds] at fitsW
          cases fitsW
        show x :: xs.erase w = (x :: xs).erase w
        rw [List.erase_cons, show (x == w) = false from decide_eq_false other,
          if_neg Bool.false_ne_true]

/-- Whether a list has no entry, as a step tests it: by its length. -/
theorem decide_length_zero {α : Type} : ∀ (l : List α), decide (l.length = 0) = l.isEmpty
  | [] => rfl
  | _ :: _ => rfl

end List

end Effect4.Constructive
