import OCaml5.Lib.Sexp

/-!
# `OCaml5.Lib.Derived` — the `ppx_jane` derivers as specifications

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§4.4: "ppx-generated code is admitted only as the plain OCaml it expands to … the profile lists
them with the laws we rely on: `compare` total order, `sexp_of`/`of_sexp` round trip,
`Fields.fold` visiting every field once in declaration order". Report:
`docs/research/2026-09-04-seat-w4-library-carriers.md`.

A deriver is not a value: `[@@deriving compare]` writes a *function* into the module. What a
carrier can state is the **contract** that function satisfies, and that is what this module is:
one record per deriver family (`Derived`), one predicate saying it is lawful (`Derived.Lawful`),
and a **canonical construction** (`Derived.ofSexp`) that is proved lawful, so a generated carrier
instantiates the template by exhibiting an injective `sexp_of` and nothing else.

## Named properties (theorem names are stable; cite these)

* `Derived.Lawful` — the whole contract, as one predicate: total order, equality agreement, hash
  determined by the sexp.
* `Derived.ofSexp_lawful` — **the template**: an injective `sexp_of` yields a lawful
  `compare` / `equal` / `hash`. This is the theorem a generated carrier instantiates.
* `Derived.compare_eq_iff_eq` — `compare a b = 0 ↔ a = b` for any lawful deriver (`compare` is
  consistent with structural equality).
* `Derived.equal_iff_compare_eq` — `equal` agrees with `compare = 0`.
* `Derived.hash_eq_of_eq` — equal values hash equally (`hash` is a function of the sexp).
* `Fields.fold_visits_each_field_once` — `Fields.fold` accumulating the field names reproduces
  the description's fields, in **declaration order**.
* `Fields.fold_length` — and it performs exactly one step per field.
* `Variants.toRank_eq_index` — `Variants.to_rank` is the constructor's index in declaration
  order.
* `Variants.toRank_inj` — distinct constructors get distinct ranks.
* `Variants.rank_lt_length` — a rank is a legal index.

## What each definition stands for

| here | `ppx_jane` | the law we rely on |
| --- | --- | --- |
| `Derived.sexpOf` | `[@@deriving sexp_of]`, i.e. `ppx_sexp_conv` | `Lawful.sexp_inj`; the shapes are `OCaml5.Lib.SexpOf` |
| `Derived.compare` | `[@@deriving compare]`, i.e. `ppx_compare` | `Lawful` total order |
| `Derived.equal` | `[@@deriving equal]` | `Lawful.equal_compare` |
| `Derived.hash` | `[@@deriving hash]`, i.e. `ppx_hash` | `Lawful.hash_of_sexp` |
| `Fields.fold` | `[@@deriving fields]`, `Fields.fold`/`Fields.iter` (`fieldslib`) | `fold_visits_each_field_once` |
| `Variants.toRank` | `[@@deriving variants]`, `Variants.to_rank` (`variantslib`) | `toRank_eq_index` |

## Refusals

* **`ppx_compare`'s actual order.** We rely on `compare` being *a* total order consistent with
  equality, not on *which* order. `Derived.ofSexp` picks the printed-sexp order; a generated
  OCaml `compare` picks the structural one. Anything that depends on the specific order (a sorted
  output, a `Map` iteration order across the Lean/OCaml boundary) is outside the contract.
  Refusal row `W4-DERIVED-COMPARE-ORDER`.
* **`ppx_hash`'s actual hash.** Only "a function of the sexp" is claimed — never a value, never a
  collision bound, never stability across versions. Refusal row `W4-DERIVED-HASH-VALUE`.
* **`of_sexp` failure.** `t_of_sexp` raises `Of_sexp_error` on a malformed sexp; the carrier's
  round trip is stated in the `sexp_of` direction plus injectivity, which is what a *writer*
  needs. A reader of untrusted sexps is a partial function and gets no law here. Refusal row
  `W4-DERIVED-OF-SEXP-PARTIAL`.
* **`Fields.iter` with mutable setters, `Field.fset`, `Variants.map` with functions.** The
  first-order fold is modelled; the higher-order faces are not. Refusal row
  `W4-DERIVED-HIGHER-ORDER`.
* **`ppx_enumerate`, `ppx_let`, `ppx_here`.** No carrier: `enumerate` needs a finiteness fact the
  descriptions do not carry, `let` and `here` are syntax. Refusal row `W4-DERIVED-OTHER-PPX`.
-/

set_option autoImplicit false

namespace OCaml5.Lib

universe u

open OCaml5.Ml

/-! ## The deriver family, as one record -/

/-- What `[@@deriving sexp, compare, equal, hash]` writes into a module. -/
structure Derived (α : Type u) : Type u where
  /-- `sexp_of_t`. -/
  sexpOf : α → Sexp
  /-- `compare`, as its sign. -/
  compare : α → α → Ordering
  /-- `equal`. -/
  equal : α → α → Bool
  /-- `hash`. -/
  hash : α → Nat

namespace Derived

variable {α : Type u}

/-- The contract every generated carrier must satisfy. -/
structure Lawful (d : Derived α) : Prop where
  /-- `sexp_of_t` names the value. -/
  sexp_inj : ∀ a b : α, d.sexpOf a = d.sexpOf b → a = b
  /-- `compare x x = 0`. -/
  compare_self : ∀ a : α, d.compare a a = .eq
  /-- **Consistent with structural equality.** -/
  eq_of_compare_eq : ∀ a b : α, d.compare a b = .eq → a = b
  /-- The sign flips. -/
  compare_swap : ∀ a b : α, d.compare b a = (d.compare a b).swap
  /-- `<` is transitive: with the two above, `compare` is a total order. -/
  compare_trans : ∀ a b c : α, d.compare a b = .lt → d.compare b c = .lt → d.compare a c = .lt
  /-- **`equal` agrees with `compare = 0`.** -/
  equal_compare : ∀ a b : α, d.equal a b = (d.compare a b == Ordering.eq)
  /-- **`hash` is a function of the sexp.** -/
  hash_of_sexp : ∀ a b : α, d.sexpOf a = d.sexpOf b → d.hash a = d.hash b

/-- A lawful deriver's `compare` is a `LinOrd`. -/
@[instance_reducible] def toLinOrd (d : Derived α) (h : Lawful d) : LinOrd α where
  cmp := d.compare
  cmp_self := h.compare_self
  eq_of_cmp_eq {a b} hc := h.eq_of_compare_eq a b hc
  cmp_swap := h.compare_swap
  cmp_trans_lt {a b c} h₁ h₂ := h.compare_trans a b c h₁ h₂

/-- **`compare` is consistent with structural equality.** -/
theorem compare_eq_iff_eq {d : Derived α} (h : Lawful d) (a b : α) :
    d.compare a b = .eq ↔ a = b :=
  ⟨h.eq_of_compare_eq a b, fun hab => hab ▸ h.compare_self a⟩

/-- **`equal` agrees with `compare = 0`, hence with equality.** -/
theorem equal_iff_compare_eq {d : Derived α} (h : Lawful d) (a b : α) :
    d.equal a b = true ↔ d.compare a b = .eq := by
  rw [h.equal_compare]
  simp

theorem equal_iff_eq {d : Derived α} (h : Lawful d) (a b : α) :
    d.equal a b = true ↔ a = b :=
  (equal_iff_compare_eq h a b).trans (compare_eq_iff_eq h a b)

/-- **Equal values hash equally.** -/
theorem hash_eq_of_eq {d : Derived α} (h : Lawful d) {a b : α} (hab : a = b) :
    d.hash a = d.hash b := h.hash_of_sexp a b (hab ▸ rfl)

/-! ### The template a generated carrier instantiates -/

/-- The canonical deriver over an injective `sexp_of`: compare by the canonical sexp text, equal
by that comparison, hash by a function of the sexp. -/
def ofSexp (sexpOf : α → Sexp) (hash : Sexp → Nat) : Derived α where
  sexpOf := sexpOf
  compare a b := LinOrd.cmp (sexpOf a) (sexpOf b)
  equal a b := LinOrd.cmp (sexpOf a) (sexpOf b) == Ordering.eq
  hash a := hash (sexpOf a)

/-- **The template.** An injective `sexp_of` yields a lawful `compare` / `equal` / `hash`; a
generated carrier discharges the whole contract by exhibiting that one fact. -/
theorem ofSexp_lawful (sexpOf : α → Sexp) (hash : Sexp → Nat)
    (hinj : ∀ a b : α, sexpOf a = sexpOf b → a = b) :
    Lawful (ofSexp sexpOf hash) where
  sexp_inj := hinj
  compare_self a := LinOrd.cmp_self (sexpOf a)
  eq_of_compare_eq a b h := hinj a b (LinOrd.eq_of_cmp_eq h)
  compare_swap a b := LinOrd.cmp_swap (sexpOf a) (sexpOf b)
  compare_trans _ _ _ h₁ h₂ := LinOrd.cmp_trans_lt h₁ h₂
  equal_compare _ _ := rfl
  hash_of_sexp a b h := by
    have h' : sexpOf a = sexpOf b := h
    simp only [ofSexp, h']

end Derived

/-! ## `[@@deriving fields]` -/

namespace Fields

/-- `Fields.fold ~init ~f`: the mechanical field-by-field walk, in declaration order. `fieldslib`
passes each `Field.t` in the order the record declares them; the description's `fields` list is
that order. -/
def fold {β : Type u} (d : StructDesc) (init : β) (f : β → FieldDesc → β) : β :=
  d.fields.foldl f init

/-- `Fields.iter`, as the fold that keeps nothing. -/
def iter (d : StructDesc) (f : FieldDesc → Unit) : Unit :=
  fold d () (fun _ fd => f fd)

/-- The declared field names, in order. -/
def names (d : StructDesc) : List String := d.fields.map (·.leanName)

private theorem foldl_snoc :
    ∀ (l : List FieldDesc) (acc : List String),
      l.foldl (fun a (fd : FieldDesc) => a ++ [fd.leanName]) acc = acc ++ l.map (·.leanName)
  | [], acc => by simp
  | e :: r, acc => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_snoc r (acc ++ [e.leanName])]
    simp

/-- **`Fields.fold` visits every field exactly once, in declaration order.** -/
theorem fold_visits_each_field_once (d : StructDesc) :
    fold d ([] : List String) (fun acc fd => acc ++ [fd.leanName]) = names d := by
  simp [fold, names, foldl_snoc d.fields []]

private theorem foldl_count :
    ∀ (l : List FieldDesc) (n : Nat),
      l.foldl (fun (a : Nat) (_ : FieldDesc) => a + 1) n = n + l.length
  | [], n => by simp
  | _ :: r, n => by
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_count r (n + 1)]
    omega

/-- **And exactly one step per field.** -/
theorem fold_length (d : StructDesc) :
    fold d 0 (fun n _ => n + 1) = d.fields.length := by
  simp [fold, foldl_count d.fields 0]

/-- The description's field names are distinct. Not automatic: it is a fact about the
description, and it is what makes `fold`'s visit a *bijection* onto the fields rather than only a
list. `OCaml5.Ml.Check` is where a generator is made to guarantee it. -/
def namesNodup (d : StructDesc) : Prop := (names d).Nodup

/-- With distinct names, the fold's output has no repeat either. -/
theorem fold_nodup (d : StructDesc) (h : namesNodup d) :
    (fold d ([] : List String) (fun acc fd => acc ++ [fd.leanName])).Nodup := by
  rw [fold_visits_each_field_once]; exact h

end Fields

/-! ## `[@@deriving variants]` -/

namespace Variants

/-- The OCaml constructor names, in declaration order. -/
def names (d : InductiveDesc) : List String := SexpOf.ctorNames d

/-- Position of a name in a list. -/
def indexOfName : List String → String → Option Nat
  | [], _ => none
  | x :: r, n => if x = n then some 0 else (indexOfName r n).map (· + 1)

/-- `Variants.to_rank`: the constructor's index in declaration order. -/
def toRank (d : InductiveDesc) (ctor : String) : Option Nat := indexOfName (names d) ctor

/-- `Variants.descriptions`: the constructor names paired with their ranks. -/
def descriptions (d : InductiveDesc) : List (String × Nat) :=
  (names d).zip (List.range (names d).length)

private theorem indexOfName_getElem :
    ∀ (l : List String), l.Nodup → ∀ (i : Nat) (c : String), l[i]? = some c →
      indexOfName l c = some i
  | [], _, _, _, h => by simp at h
  | x :: r, hnd, i, c, h => by
    have hnd' := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      simp [indexOfName, h]
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      have hne : x ≠ c := by
        intro hc
        exact hnd'.1 (hc ▸ List.mem_of_getElem? h)
      simp only [indexOfName, if_neg hne]
      rw [indexOfName_getElem r hnd'.2 i' c h]
      rfl

/-- **`Variants.to_rank` is the constructor's index.** -/
theorem toRank_eq_index (d : InductiveDesc) (h : (names d).Nodup) (i : Nat) (c : String)
    (hc : (names d)[i]? = some c) : toRank d c = some i :=
  indexOfName_getElem (names d) h i c hc

private theorem indexOfName_lt :
    ∀ (l : List String) (c : String) (i : Nat), indexOfName l c = some i → i < l.length
  | [], _, _, h => by simp [indexOfName] at h
  | x :: r, c, i, h => by
    by_cases hx : x = c
    · simp only [indexOfName, if_pos hx, Option.some.injEq] at h
      simp [← h]
    · simp only [indexOfName, if_neg hx, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, hij⟩ := h
      have := indexOfName_lt r c j hj
      simp only [List.length_cons]
      omega

/-- A rank is a legal index. -/
theorem rank_lt_length (d : InductiveDesc) (c : String) (i : Nat) (h : toRank d c = some i) :
    i < (names d).length := indexOfName_lt (names d) c i h

private theorem indexOfName_inj :
    ∀ (l : List String) (c₁ c₂ : String) (i : Nat),
      indexOfName l c₁ = some i → indexOfName l c₂ = some i → c₁ = c₂
  | [], _, _, _, h, _ => by simp [indexOfName] at h
  | x :: r, c₁, c₂, i, h₁, h₂ => by
    by_cases hx₁ : x = c₁
    · by_cases hx₂ : x = c₂
      · rw [← hx₁, ← hx₂]
      · exfalso
        simp only [indexOfName, if_pos hx₁, Option.some.injEq] at h₁
        simp only [indexOfName, if_neg hx₂, Option.map_eq_some_iff] at h₂
        obtain ⟨j, _, hij⟩ := h₂
        omega
    · by_cases hx₂ : x = c₂
      · exfalso
        simp only [indexOfName, if_pos hx₂, Option.some.injEq] at h₂
        simp only [indexOfName, if_neg hx₁, Option.map_eq_some_iff] at h₁
        obtain ⟨j, _, hij⟩ := h₁
        omega
      · simp only [indexOfName, if_neg hx₁, Option.map_eq_some_iff] at h₁
        simp only [indexOfName, if_neg hx₂, Option.map_eq_some_iff] at h₂
        obtain ⟨j₁, hj₁, hij₁⟩ := h₁
        obtain ⟨j₂, hj₂, hij₂⟩ := h₂
        have : j₁ = j₂ := by omega
        exact indexOfName_inj r c₁ c₂ j₁ hj₁ (this ▸ hj₂)

/-- **Distinct constructors get distinct ranks.** -/
theorem toRank_inj (d : InductiveDesc) (c₁ c₂ : String) (i : Nat)
    (h₁ : toRank d c₁ = some i) (h₂ : toRank d c₂ = some i) : c₁ = c₂ :=
  indexOfName_inj (names d) c₁ c₂ i h₁ h₂

end Variants

end OCaml5.Lib
