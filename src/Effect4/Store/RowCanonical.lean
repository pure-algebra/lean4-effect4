import Effect4.Store.Canonical
import Effect4.Data.Row

/-!
# Exact images for canonical finite rows

A row is a sorted list with a proof. Reuse Image.subtype and Image.equiv: bytes keep
list framing, while decoding refuses a list that does not satisfy strict ascent.
No proof is serialized, and decoding never sorts or silently removes duplicates.
-/

namespace Effect4.Store

variable {α : Type} [LT α] [DecidableLT α] [Canonical α]

/-- The existing list image restricted to its strictly ascending members. -/
def rowImage : Image (Effect4.Row α) :=
  ((Canonical.image (List α)).subtype Effect4.Ascending).equiv
    (fun r => ⟨r.val, r.property⟩)
    (fun r => ⟨r.elems, r.ascending⟩)
    (fun r => by cases r; rfl)
    (fun r => by cases r; rfl)

instance instCanonicalRow : Canonical (Effect4.Row α) where
  shape := Canonical.shape (List α)
  toVal := rowImage.toVal
  ofVal := rowImage.ofVal
  ofVal_toVal := rowImage.ofVal_toVal
  ofVal_exact := rowImage.ofVal_exact
  fits r := Canonical.fits r.elems

#print axioms rowImage
#print axioms instCanonicalRow

end Effect4.Store
