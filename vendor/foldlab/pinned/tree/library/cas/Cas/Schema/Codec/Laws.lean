import Cas.Schema.Codec.Laws.Mutual
import Cas.Schema.Codec.Laws.Render

/-!
# Consequences of the schema codec laws

Small public consequences derived from the forward and image-exactness
law families.
-/

namespace Cas.Schema

/-- One value representation per described value — the corollary that
makes every `El a` addressable through the canonical rendering. -/
theorem encode_inj {a : Ast} (ha : a.WF) {x y : El a}
    (h : encode a x = encode a y) : x = y := by
  have h1 := decode_encode a ha x
  rw [h, decode_encode a ha y] at h1
  injection h1 with h1
  exact h1.symm

/-! ## JSON exactness — derived -/

/-- Unique JSON representative: two JSON values decoding to the same
described value ARE the same value. Exactness, phrased as the identity
law the store needs. -/
theorem json_exact {a : Ast} {v w : Json.Value} {x : El a}
    (hv : decode a v = some x) (hw : decode a w = some x) : v = w := by
  rw [decode_exact hv, decode_exact hw]

/-- One canonical rendering per described value: anything the decoder
accepts for `x` renders to the bytes of `encode a x` — the string the
content identity is computed over is unique. -/
theorem json_exact_render {a : Ast} {v : Json.Value} {x : El a}
    (hv : decode a v = some x) :
    Json.renderCompact v = Json.renderCompact (encode a x) := by
  rw [decode_exact hv]

/-- Decoding is injective in the value: distinct described values never
share a JSON representative. -/
theorem decode_inj {a : Ast} {v : Json.Value} {x y : El a}
    (hx : decode a v = some x) (hy : decode a v = some y) : x = y := by
  rw [hx] at hy
  injection hy

end Cas.Schema
