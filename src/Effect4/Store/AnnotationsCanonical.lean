import Effect4.Store.Canonical
import Effect4.Machine.Value

/-!
# The canonical instance of a reason's annotations

`ReasonAnnotations` (`Machine/Cause.lean`) is an entry list with a proof that its keys are
distinct. The generator cannot write its instance, because a `Prop` field is not a carrier.
This is the one written by hand: the writer and the reader are `Value.annotations`, the image
the machine already uses, so the bytes are the ones the generator would write for the data
field (the entry list under `ctor 0`), and reading decides the key condition again. No proof is
serialized, and reading never drops or reorders a duplicate: it refuses.

With this instance in scope the generator derives `Reason`, `Cause`, `Exit`, `Completion` and
the decision alphabet by its ordinary rule.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4.Machine

variable {α : Type} [Canonical α]

/-- The machine's annotation image, over the instance's image of the annotation values. -/
def annotationsImage : Image (Effect4.ReasonAnnotations α) :=
  Value.annotations (Canonical.image α)

theorem annotationsImage_toVal (r : Effect4.ReasonAnnotations α) :
    (annotationsImage (α := α)).toVal r = .ctor 0 [Canonical.toVal r.entries] := rfl

instance instCanonicalReasonAnnotations : Canonical (Effect4.ReasonAnnotations α) where
  shape :=
    ⟨.struct "ReasonAnnotations" [("entries", (Canonical.shape (List (String × α))).root)],
     (Canonical.shape (List (String × α))).defs⟩
  toVal := annotationsImage.toVal
  ofVal := annotationsImage.ofVal
  ofVal_toVal := annotationsImage.ofVal_toVal
  ofVal_exact := annotationsImage.ofVal_exact
  fits r := by
    rw [annotationsImage_toVal]
    apply accepts_struct
    exact acceptsFields_cons _ _ _ _ _ _ (Canonical.fits r.entries) (acceptsFields_nil _)

end Effect4.Store
