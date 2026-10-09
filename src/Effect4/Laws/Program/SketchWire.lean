import Effect4.Program.SketchWire
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.SketchWire — a sketch's bytes are an exact embedding

`Program/SketchWire.lean` writes a sketch as its program's canonical bytes and its hole table's.
This module holds the two laws of an exact embedding: a well-formed sketch reads back, and
whatever reads was that sketch's bytes.

## Placement

Concept `exact-codecs`; property: a carrier's canonical bytes are an exact embedding, and a pair
of exact embeddings is one. Requirement R14 (program as data), under decisions row 305, point 3.

- **`sketch-wire`** (claim, role compatibility; pointer `Sketch.decode_exact`). Reach: every
  sketch whose two value trees are well-formed. Not established: a stored sketch's renumbering
  when its application gains a row (`sketch-renumbering`); the admission of the hole table
  (`sketch-admission`). Consumer: the query tool, whose requests carry a hole table and whose
  omission answers carry the grown one.
-/

set_option autoImplicit false

namespace Effect4.Program.Sketch

open Effect4 Effect4.Store

/-- **Round trip**: a sketch whose two value trees are well-formed reads back. A step of
`sketch-wire`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem decode_encode (s : Sketch) (hp : (Canonical.toVal s.program).WF)
    (hh : (Canonical.toVal s.holes).WF) : decode (encode s) = some s := by
  simp only [decode, encode, Wire.decodeHoles, Wire.encodeHoles, Wire.decode_encode _ hp,
    Canonical.decode_encode _ hh, Option.bind_some, Option.map_some]

/-- **Exactness**: whatever reads as a sketch was that sketch's bytes, and its value trees are
well-formed. The pointer of `sketch-wire`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem decode_exact {b : Bytes × Bytes} {s : Sketch} (h : decode b = some s) :
    b = encode s ∧ (Canonical.toVal s.program).WF ∧ (Canonical.toVal s.holes).WF := by
  obtain ⟨b₁, b₂⟩ := b
  simp only [decode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨program, hp, holes, hh, rfl⟩ := h
  obtain ⟨rfl, hwp⟩ := Wire.decode_exact hp
  obtain ⟨rfl, hwh⟩ := Canonical.decode_exact hh
  exact ⟨rfl, hwp, hwh⟩

end Effect4.Program.Sketch
