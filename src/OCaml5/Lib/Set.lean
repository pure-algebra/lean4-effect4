import OCaml5.Lib.Map

/-!
# `OCaml5.Lib.Set` — the carrier for `Base.Set`

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§4.2. Report: `docs/research/2026-09-04-seat-w4-library-carriers.md`.

`Base.Set.t` is `Base.Map.t` with `unit` data — that is literally how `base/src/set.ml` is built
on `Map.Tree` — so this carrier is `OCaml5.Lib.Map κ Unit` with a `mem` face. Every law below is
the corresponding `Map` law read through `Set.mem_iff_find`.

## Named properties (theorem names are stable; cite these)

* `Set.mem_empty` — `mem empty x = false`.
* `Set.mem_add_same` — `mem (add s x) x = true`.
* `Set.mem_add_other` — `y ≠ x → mem (add s x) y = mem s y`.
* `Set.mem_remove_same` — `mem (remove s x) x = false`.
* `Set.mem_remove_other` — `y ≠ x → mem (remove s x) y = mem s y`.
* `Set.ext_mem` — two sets with the same members are equal (canonical form).
* `Set.add_comm` — `add` at two distinct elements commutes.
* `Set.add_idem` — `add` twice is `add` once.
* `Set.toList_sorted` — `to_list` is strictly ascending.
* `Set.toList_nodup` — every element occurs exactly once.
* `Set.ofList_toList` — `of_list ∘ to_list = id`.
* `Set.fold_visits_elements_in_order` — `fold` accumulating the elements reproduces `to_list`.
* `Set.mem_union`, `Set.mem_inter`, `Set.mem_diff` — the three set operations are pointwise.

## What each definition stands for

| here | `Base` | the law |
| --- | --- | --- |
| `Set.empty` | `Set.empty ~comparator` | `mem_empty` |
| `Set.mem` | `Set.mem : ('a,_) t -> 'a -> bool` | `mem_add_same`, `mem_add_other` |
| `Set.add` | `Set.add : t -> 'a -> t` | `mem_add_same`, `mem_add_other`, `add_idem` |
| `Set.remove` | `Set.remove : t -> 'a -> t` | `mem_remove_same`, `mem_remove_other` |
| `Set.fold` | `Set.fold : t -> init:'b -> f:('b -> 'a -> 'b) -> 'b`, "in increasing order" | `fold_visits_elements_in_order` |
| `Set.toList` | `Set.to_list` (= `elements`, increasing) | `toList_sorted`, `toList_nodup` |
| `Set.ofList` | `Set.of_list` | `ofList_toList` |
| `Set.union` / `inter` / `diff` | `Set.union` / `inter` / `diff` | `mem_union`, `mem_inter`, `mem_diff` |
| `Set.length` | `Set.length` | — |

## Refusals

* **`Set.min_elt` / `max_elt` / `nth` / the `Tree` module.** As for `Map`. Refusal row
  `W4-SET-TREE-ORDER`.
* **`Set.symmetric_diff` and the `Sequence`-returning operations.** No carrier: they hand back a
  `Sequence.t`, which is refused in `OCaml5.Lib.Stream` (`W4-STREAM-SEQUENCE`). Refusal row
  `W4-SET-SEQUENCE`.
* **`Set.equal` across two comparators.** As `W4-MAP-COMPARATOR-VALUE`.
-/

set_option autoImplicit false

namespace OCaml5.Lib

universe u

/-- `Base.Set.t`: a `Map` whose data is `unit` (`base/src/set.ml`). -/
structure Set (κ : Type u) [LinOrd κ] : Type u where
  /-- The underlying map. -/
  toMap : Map κ Unit

namespace Set

variable {κ : Type u} [LinOrd κ]

@[ext] theorem ext {s₁ s₂ : Set κ} (h : s₁.toMap = s₂.toMap) : s₁ = s₂ := by
  cases s₁; cases s₂; cases h; rfl

instance [DecidableEq κ] : DecidableEq (Set κ) := fun s₁ s₂ =>
  if h : s₁.toMap = s₂.toMap then .isTrue (ext h)
  else .isFalse fun he => h (congrArg Set.toMap he)

/-- `Base.Set.empty`. -/
def empty : Set κ := ⟨Map.empty⟩

/-- `Base.Set.mem`. -/
def mem (s : Set κ) (x : κ) : Bool := (s.toMap.find x).isSome

/-- `Base.Set.add`. -/
def add (s : Set κ) (x : κ) : Set κ := ⟨s.toMap.set x ()⟩

/-- `Base.Set.remove`. -/
def remove (s : Set κ) (x : κ) : Set κ := ⟨s.toMap.remove x⟩

/-- `Base.Set.to_list` / `elements`, in increasing order. -/
def toList (s : Set κ) : List κ := s.toMap.keys

/-- `Base.Set.of_list`. -/
def ofList (l : List κ) : Set κ := ⟨Map.ofAlist (l.map fun x => (x, ()))⟩

/-- `Base.Set.length`. -/
def length (s : Set κ) : Nat := s.toMap.length

/-- `Base.Set.fold ~init ~f`, "in increasing order". -/
def fold {β : Type u} (s : Set κ) (init : β) (f : κ → β → β) : β :=
  s.toMap.fold init (fun k _ acc => f k acc)

/-- The `merge` function of `Base.Set.union`. -/
private def unionF (_ : κ) (a b : Option Unit) : Option Unit :=
  match a, b with
  | none, none => none
  | _, _ => some ()

/-- The `merge` function of `Base.Set.inter`. -/
private def interF (_ : κ) (a b : Option Unit) : Option Unit :=
  match a, b with
  | some _, some _ => some ()
  | _, _ => none

/-- The `merge` function of `Base.Set.diff`. -/
private def diffF (_ : κ) (a b : Option Unit) : Option Unit :=
  match a, b with
  | some _, none => some ()
  | _, _ => none

/-- `Base.Set.union`. -/
def union (s₁ s₂ : Set κ) : Set κ := ⟨Map.merge unionF s₁.toMap s₂.toMap⟩

/-- `Base.Set.inter`. -/
def inter (s₁ s₂ : Set κ) : Set κ := ⟨Map.merge interF s₁.toMap s₂.toMap⟩

/-- `Base.Set.diff`. -/
def diff (s₁ s₂ : Set κ) : Set κ := ⟨Map.merge diffF s₁.toMap s₂.toMap⟩

/-! ### The laws -/

theorem mem_iff_find (s : Set κ) (x : κ) : s.mem x = (s.toMap.find x).isSome := rfl

@[simp] theorem mem_empty (x : κ) : (empty : Set κ).mem x = false := rfl

@[simp] theorem mem_add_same (s : Set κ) (x : κ) : (s.add x).mem x = true := by
  simp [mem, add]

theorem mem_add_other (s : Set κ) (x y : κ) (h : y ≠ x) : (s.add x).mem y = s.mem y := by
  simp [mem, add, Map.find_set_other _ _ _ _ h]

@[simp] theorem mem_remove_same (s : Set κ) (x : κ) : (s.remove x).mem x = false := by
  simp [mem, remove]

theorem mem_remove_other (s : Set κ) (x y : κ) (h : y ≠ x) : (s.remove x).mem y = s.mem y := by
  simp [mem, remove, Map.find_remove_other _ _ _ h]

/-- **Canonical form.** A `Map κ Unit`'s data carries no information, so equal membership is
equal maps. -/
theorem ext_mem {s₁ s₂ : Set κ} (h : ∀ x, s₁.mem x = s₂.mem x) : s₁ = s₂ := by
  refine ext (Map.ext_find fun k => ?_)
  have := h k
  simp only [mem] at this
  cases h₁ : s₁.toMap.find k with
  | none => cases h₂ : s₂.toMap.find k with
    | none => rfl
    | some b => rw [h₁, h₂] at this; simp at this
  | some a => cases h₂ : s₂.toMap.find k with
    | none => rw [h₁, h₂] at this; simp at this
    | some b => cases a; cases b; rfl

theorem add_comm (s : Set κ) {x y : κ} (h : x ≠ y) : (s.add x).add y = (s.add y).add x :=
  ext (Map.set_comm s.toMap () () h)

theorem add_idem (s : Set κ) (x : κ) : (s.add x).add x = s.add x :=
  ext (Map.set_set_same s.toMap x () ())

/-- **`to_list` is strictly ascending.** -/
theorem toList_sorted (s : Set κ) : strictAsc s.toMap.entries = true := s.toMap.wf

/-- **Every element occurs exactly once.** -/
theorem toList_nodup (s : Set κ) : s.toList.Nodup := Map.keys_nodup s.toMap

/-- **`fold` visits every element exactly once, in increasing order.** -/
theorem fold_visits_elements_in_order (s : Set κ) :
    s.fold ([] : List κ) (fun x acc => acc ++ [x]) = s.toList :=
  Map.fold_visits_keys_in_order s.toMap

private theorem toAlist_map (s : Set κ) : s.toList.map (fun x => (x, ())) = s.toMap.toAlist := by
  simp only [toList, Map.keys, Map.toAlist, List.map_map]
  induction s.toMap.entries with
  | nil => rfl
  | cons e r ih =>
    simp only [List.map_cons, ih, Function.comp]

/-- **`of_list ∘ to_list = id`.** -/
theorem ofList_toList (s : Set κ) : ofList s.toList = s := by
  refine ext ?_
  rw [ofList, toAlist_map s, Map.ofAlist_toAlist]

/-! ### The three set operations, pointwise -/

@[simp] theorem mem_union (s₁ s₂ : Set κ) (x : κ) :
    (s₁.union s₂).mem x = (s₁.mem x || s₂.mem x) := by
  simp only [mem, union]
  rw [Map.find_merge unionF s₁.toMap s₂.toMap x rfl]
  cases s₁.toMap.find x <;> cases s₂.toMap.find x <;> rfl

@[simp] theorem mem_inter (s₁ s₂ : Set κ) (x : κ) :
    (s₁.inter s₂).mem x = (s₁.mem x && s₂.mem x) := by
  simp only [mem, inter]
  rw [Map.find_merge interF s₁.toMap s₂.toMap x rfl]
  cases s₁.toMap.find x <;> cases s₂.toMap.find x <;> rfl

@[simp] theorem mem_diff (s₁ s₂ : Set κ) (x : κ) :
    (s₁.diff s₂).mem x = (s₁.mem x && !s₂.mem x) := by
  simp only [mem, diff]
  rw [Map.find_merge diffF s₁.toMap s₂.toMap x rfl]
  cases s₁.toMap.find x <;> cases s₂.toMap.find x <;> rfl

end Set

end OCaml5.Lib
