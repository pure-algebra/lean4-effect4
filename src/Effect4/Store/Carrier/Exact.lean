module

public import Effect4.Store.Carrier.Image

/-!
# Store.Exact

Owner: the dictionary's exact embedding (`docs/core/controlled-english.md` §3.5) as a carrier:
a write `α → β`, a read `β → Option α`, the domain the pair is total on, the retraction on that
domain, and exactness everywhere. The normaliser is the identity.

An `Image α` (`src/Effect4/Store/Carrier/Image.lean`) is an exact embedding into `Val` with the
whole carrier as its domain (`ofImage`). The store node codec is one into `Bytes` on the
well-formed values, and program admission is one from `Built` into `Object`
(`src/Effect4/Laws/Api/Object.lean`).

Exact embeddings compose (`comp`): write forward, read backward through both, on the domain
where both retract. A load of a saved program is the composite of forgetting its certificate
and writing its node, so its two laws are the composite's.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

/-- An exact embedding: total on its domain, a retraction there, exact everywhere. -/
structure Exact (α β : Type) where
  /-- The write. -/
  write : α → β
  /-- The read, `none` outside the image. -/
  read : β → Option α
  /-- The domain the pair is total on. -/
  dom : α → Prop
  /-- Every image of the domain reads back. -/
  retract : ∀ a, dom a → read (write a) = some a
  /-- Nothing outside the image reads. -/
  exact : ∀ {b a}, read b = some a → b = write a

namespace Exact

variable {α β γ : Type}

/-- Exact embeddings compose: write forward, read backward through both. -/
def comp (f : Exact α β) (g : Exact β γ) : Exact α γ where
  write a := g.write (f.write a)
  read c := (g.read c).bind f.read
  dom a := f.dom a ∧ g.dom (f.write a)
  retract a h := by
    rw [g.retract _ h.2, Option.bind_some, f.retract a h.1]
  exact := by
    intro c a h
    obtain ⟨b, hb, ha⟩ := Option.bind_eq_some_iff.mp h
    rw [g.exact hb, f.exact ha]

/-- An image is an exact embedding into the value tree, on the whole carrier. -/
def ofImage (I : Image α) : Exact α Val where
  write := I.toVal
  read := I.ofVal
  dom _ := True
  retract a _ := I.ofVal_toVal a
  exact h := I.ofVal_exact h

end Exact

end Effect4.Store
