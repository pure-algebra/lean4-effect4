import Cas.Schema.Codec

/-!
# Native types described by schema codes

`Described α` pairs a native Lean carrier with a well-formed schema
code and an equivalence to that code's denotation. The existing generic
codec therefore supplies encoding, decoding, and their laws uniformly.
-/

namespace Cas.Schema

/-- A native Lean type represented exactly by one well-formed schema
code. This is stronger than a serializer: `toEl` and `ofEl` record
both directions and their inverse laws. -/
class Described (α : Type u) where
  code : Ast
  wf : code.WF
  toEl : α → El code
  ofEl : El code → α
  ofEl_toEl : ∀ x, ofEl (toEl x) = x
  toEl_ofEl : ∀ x, toEl (ofEl x) = x

namespace Described

/-- Encode through a type's schema representation. -/
def encode {α : Type u} [d : Described α] (x : α) : Json.Value :=
  Cas.Schema.encode d.code (d.toEl x)

/-- Decode through a type's schema representation. -/
def decode {α : Type u} [d : Described α] (v : Json.Value) : Option α :=
  (Cas.Schema.decode d.code v).map d.ofEl

theorem decode_encode {α : Type u} [d : Described α] (x : α) :
    decode (encode x) = some x := by
  simp only [decode, encode, Cas.Schema.decode_encode d.code d.wf,
    Option.map_some, d.ofEl_toEl]

theorem decode_exact {α : Type u} [d : Described α]
    {v : Json.Value} {x : α} (h : decode v = some x) :
    v = encode x := by
  simp only [decode] at h
  cases hd : Cas.Schema.decode d.code v with
  | none =>
    rw [hd] at h
    exact nomatch h
  | some y =>
    rw [hd] at h
    simp only [Option.map_some] at h
    injection h with hx
    subst hx
    rw [Cas.Schema.decode_exact hd]
    simp only [encode, d.toEl_ofEl]

theorem encode_inj {α : Type u} [d : Described α] {x y : α}
    (h : encode x = encode y) : x = y := by
  have he : d.toEl x = d.toEl y := Cas.Schema.encode_inj d.wf h
  calc
    x = d.ofEl (d.toEl x) := (d.ofEl_toEl x).symm
    _ = d.ofEl (d.toEl y) := congrArg d.ofEl he
    _ = y := d.ofEl_toEl y

end Described

end Cas.Schema
