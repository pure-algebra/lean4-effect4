import Conform.Layout.Types

/-!
# Conform.Layout.Laws — one theorem per admissibility condition

**What it is.** The laws the layout datum's admissibility conditions *are*. Each discrimination
rule of `Conform.Layout.Layout` carries a condition its checker decides by code; this module
states, for the abstract encoder that rule induces, the theorem "under exactly that condition
the encoder is injective", and, for the rule that fails in practice, the theorem "when the
condition is dropped these two values collide". "Obviously injective" is not a proof; this is
where the proof is.

**Depends on.** `Conform.Layout.Types` (the `TVal` target-value language). Nothing else.

**Properties.**
* `nullable_injective` / `nullable_collides` — the F1 law, both directions: a nullable option
  is injective exactly when the payload never encodes as the target's null, and when it does,
  `none` and `some a` are one target value — *proved*.
* `frame_injective`, `object_injective`, `tagged_injective`, `seq_injective`,
  `literal_injective`, `wrappingNat_collides`, `boundedNat_injective` — the conditions of the
  other rules — *proved*, axioms printed at the foot of the file.
-/

namespace Conform.Layout.Laws

open Conform.Layout

/-- What every rule's condition delivers. -/
def Injective {α : Type} (f : α → TVal) : Prop := ∀ a b, f a = f b → a = b

theorem Injective.id : Injective (fun v : TVal => v) := fun _ _ h => h

/-! ## The frame: a constructor applied to its arguments

The canonical wire (`Val.ctor i args`), OCaml's variants (`Ty_option t`) and the target's own
option all write a *frame*: a name and a list. One law serves all three. -/

def frame (name : String) (args : List TVal) : TVal := .conV name args

theorem frame_inj {n m : String} {a b : List TVal} (h : frame n a = frame m b) :
    n = m ∧ a = b := by
  unfold frame at h
  injection h with h1 h2
  exact ⟨h1, h2⟩

/-- Two frames with different names are different values: the condition of `variant`,
`indexed` and `nativeOption` is exactly that the names are pairwise distinct. -/
theorem frame_ne_of_name_ne {n m : String} (h : n ≠ m) (a b : List TVal) :
    frame n a ≠ frame m b := fun e => h (frame_inj e).1

/-! ## `nullable` — the rule that failed

`Option α` as "the payload, or the target's null". Admissible only when `α`'s own layout can
never produce the null. -/

/-- The nullable option encoder. -/
def nullable {α : Type} (e : α → TVal) : Option α → TVal
  | none => .null
  | some a => e a

/-- **The admissibility condition of `nullable`, proved.** The payload never encodes as null,
and the payload encoder is injective. -/
theorem nullable_injective {α : Type} (e : α → TVal) (he : Injective e)
    (hnull : ∀ a, e a ≠ TVal.null) : Injective (nullable e) := by
  intro a b h
  match a, b with
  | none, none => rfl
  | none, some y => exact absurd (show e y = TVal.null from h.symm) (hnull y)
  | some x, none => exact absurd (show e x = TVal.null from h) (hnull x)
  | some x, some y => exact congrArg some (he x y h)

/-- **The counterexample, proved.** Drop the condition — let one payload value encode as the
target's null — and `none` and `some a` are one target value. With `e = nullable e'` this is
the nested-option collision: `α = Option β`, `a = none`, `e a = null`. -/
theorem nullable_collides {α : Type} (e : α → TVal) (a : α) (h : e a = TVal.null) :
    nullable e none = nullable e (some a) ∧ (none : Option α) ≠ some a :=
  ⟨h.symm, fun h' => nomatch h'⟩

/-- The nesting the checker actually meets: a nullable option *inside* a nullable option. The
inner `none` is the null, so the outer `none` and `some none` are the same target value —
whatever the innermost element encoder is. -/
theorem nullable_nested_collides {α : Type} (e : α → TVal) :
    nullable (nullable e) none = nullable (nullable e) (some none) ∧
      (none : Option (Option α)) ≠ some none :=
  nullable_collides (nullable e) none rfl

/-! ## `nativeOption` — the same type carried by the target's own option

OCaml's `option` is a variant, not a null: `None` and `Some None` are different values however
deep the nesting goes. This is why the `eff/` layout does not have the collision above. -/

def nativeOption {α : Type} (noneC someC : String) (e : α → TVal) : Option α → TVal
  | none => frame noneC []
  | some a => frame someC [e a]

theorem nativeOption_injective {α : Type} (noneC someC : String) (e : α → TVal)
    (he : Injective e) (hne : noneC ≠ someC) : Injective (nativeOption noneC someC e) := by
  intro a b h
  match a, b with
  | none, none => rfl
  | none, some y => exact absurd (frame_inj h).1 hne
  | some x, none => exact absurd (frame_inj h).1 hne.symm
  | some x, some y =>
    have := (frame_inj h).2
    injection this with hx
    exact congrArg some (he x y hx)

/-- Nesting is safe with no side condition at all: this is `nativeOption_injective` applied to
itself, and it is the theorem the X2 layout cannot have. -/
theorem nativeOption_nested_distinct {α : Type} (noneC someC : String) (e : α → TVal)
    (hne : noneC ≠ someC) :
    nativeOption noneC someC (nativeOption noneC someC e) none ≠
      nativeOption noneC someC (nativeOption noneC someC e) (some none) :=
  frame_ne_of_name_ne hne [] [nativeOption noneC someC e none]

/-! ## `literalUnion` — all-nullary constructors as literals -/

def literal (tag : String) : TVal := .strV tag

theorem literal_inj {a b : String} (h : literal a = literal b) : a = b := by
  unfold literal at h
  injection h

/-! ## `object` and `tagged` — named payload fields, with and without a discriminating tag -/

def object (keys : List String) (vals : List TVal) : TVal := .objV (keys.zip vals)

theorem zip_right_inj : ∀ (ks : List String) (a b : List TVal),
    a.length = ks.length → b.length = ks.length → ks.zip a = ks.zip b → a = b
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => nomatch h
  | [], _, _ :: _, _, h, _ => nomatch h
  | _ :: _, [], _, h, _, _ => nomatch h
  | _ :: _, _, [], _, h, _ => nomatch h
  | k :: ks, x :: xs, y :: ys, hx, hy, h => by
    simp only [List.zip_cons_cons] at h
    injection h with h1 h2
    injection h1 with _ h1
    subst h1
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hx hy
    rw [zip_right_inj ks xs ys hx hy h2]

/-- **The admissibility condition of a named payload, proved**: the field list is the rule's,
so the two argument lists have the rule's length, and equal objects have equal arguments. -/
theorem object_injective (keys : List String) {a b : List TVal}
    (ha : a.length = keys.length) (hb : b.length = keys.length)
    (h : object keys a = object keys b) : a = b := by
  unfold object at h
  injection h with h
  exact zip_right_inj keys a b ha hb h

/-- A tagged object: the tag field first, the payload after. -/
def tagged (tagName tag : String) (keys : List String) (vals : List TVal) : TVal :=
  .objV ((tagName, .strV tag) :: keys.zip vals)

theorem tagged_inj {tn t t' : String} {ks ks' : List String} {vs vs' : List TVal}
    (h : tagged tn t ks vs = tagged tn t' ks' vs') : t = t' ∧ ks.zip vs = ks'.zip vs' := by
  unfold tagged at h
  injection h with h
  injection h with h1 h2
  injection h1 with _ h1
  injection h1 with h1
  exact ⟨h1, h2⟩

/-- **The admissibility condition of `tagField`, proved, part one**: distinct tags give
distinct values, so the tag decides the constructor. Part two — that no payload field is named
like the tag — is not a fact about this encoder but about the target's object literal, where a
repeated key overwrites; the checker decides it and refuses (`Layout.tagShadowed`). -/
theorem tagged_ne_of_tag_ne {tn t t' : String} (h : t ≠ t') (ks ks' : List String)
    (vs vs' : List TVal) : tagged tn t ks vs ≠ tagged tn t' ks' vs' :=
  fun e => h (tagged_inj e).1

/-- Within one constructor, a tagged object is injective in its payload. -/
theorem tagged_injective (tn t : String) (keys : List String) {a b : List TVal}
    (ha : a.length = keys.length) (hb : b.length = keys.length)
    (h : tagged tn t keys a = tagged tn t keys b) : a = b :=
  zip_right_inj keys a b ha hb (tagged_inj h).2

/-! ## `nativeSeq` and `nativeTuple` -/

def seq {α : Type} (e : α → TVal) (xs : List α) : TVal := .arrV (xs.map e)

theorem map_injective {α : Type} (e : α → TVal) (he : Injective e) :
    ∀ xs ys : List α, xs.map e = ys.map e → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons] at h
    injection h with h1 h2
    rw [he x y h1, map_injective e he xs ys h2]

theorem seq_injective {α : Type} (e : α → TVal) (he : Injective e) : Injective (seq e) := by
  intro xs ys h
  unfold seq at h
  injection h with h
  exact map_injective e he xs ys h

def tuple (vals : List TVal) : TVal := .tupV vals

theorem tuple_inj {a b : List TVal} (h : tuple a = tuple b) : a = b := by
  unfold tuple at h
  injection h

/-! ## Scalar domains

A target that narrows a scalar either *refuses* the values outside its domain — a JavaScript
`number` holds every integer below `2 ^ 53` exactly and nothing above it — or *wraps* them —
an OCaml `int` is 63 bits and arithmetic is modular. The first is injective on its domain; the
second is not injective at all, and the witness is `0` against `2 ^ bits`. -/

def boundedNat (bits n : Nat) : Option TVal := if n < 2 ^ bits then some (.numV n) else none

theorem boundedNat_injective (bits : Nat) {m n : Nat} {v : TVal}
    (hm : boundedNat bits m = some v) (hn : boundedNat bits n = some v) : m = n := by
  unfold boundedNat at hm hn
  split at hm
  · split at hn
    · injection hm with hm
      injection hn with hn
      subst hm
      injection hn with hn
      exact hn.symm
    · exact nomatch hn
  · exact nomatch hm

def wrappingNat (bits n : Nat) : TVal := .numV (n % 2 ^ bits)

/-- **A narrowing that wraps is not injective**, and the smallest witness is `0` against
`2 ^ bits`. -/
theorem wrappingNat_collides (bits : Nat) :
    wrappingNat bits 0 = wrappingNat bits (2 ^ bits) ∧ (0 : Nat) ≠ 2 ^ bits := by
  refine ⟨?_, ?_⟩
  · unfold wrappingNat
    rw [Nat.zero_mod, Nat.mod_self]
  · intro h
    have : 0 < 2 ^ bits := Nat.two_pow_pos bits
    omega

/-! ## Receipts -/

#print axioms frame_inj
#print axioms frame_ne_of_name_ne
#print axioms nullable_injective
#print axioms nullable_collides
#print axioms nullable_nested_collides
#print axioms nativeOption_injective
#print axioms nativeOption_nested_distinct
#print axioms literal_inj
#print axioms zip_right_inj
#print axioms object_injective
#print axioms tagged_inj
#print axioms tagged_ne_of_tag_ne
#print axioms tagged_injective
#print axioms map_injective
#print axioms seq_injective
#print axioms tuple_inj
#print axioms boundedNat_injective
#print axioms wrappingNat_collides

end Conform.Layout.Laws
