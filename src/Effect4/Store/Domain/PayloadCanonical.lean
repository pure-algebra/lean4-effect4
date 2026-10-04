module

public import Effect4.Store.Domain.Derived.Value
public import Effect4.Machine.Alphabets

/-!
# The canonical instance of an error payload

`Payload` (`Machine/Alphabets.lean`, decisions row 120) is a value with a proof that it is a
handle-free record frame. The generator cannot write its instance, because a `Prop` field is not a
carrier; `ReasonAnnotations` is the same case (`Store/Domain/AnnotationsCanonical.lean`). This is
the one written by hand. The writer and the reader are the value's own instance (`Canonical Val`,
the Value group) restricted by `Image.subtype`, so a payload's bytes are its value's bytes, and
reading decides `isPayload` again. No proof is serialized.

With this instance in scope the generator derives `Err` and every carrier that holds it, in the
Runner group, by its ordinary rule.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

open Effect4.Machine

/-- The payload's canonical image: the value's, restricted to payloads. -/
def payloadImage : Image Payload :=
  ((Canonical.image Val).subtype (fun v => isPayload v = true)).equiv
    (fun s => ⟨s.val, s.property⟩) (fun p => ⟨p.val, p.property⟩) (fun _ => rfl) (fun _ => rfl)

theorem payloadImage_toVal (p : Payload) : payloadImage.toVal p = Canonical.toVal p.val := rfl

instance instCanonicalPayload : Canonical Payload where
  shape := Canonical.shape Val
  toVal := payloadImage.toVal
  ofVal := payloadImage.ofVal
  ofVal_toVal := payloadImage.ofVal_toVal
  ofVal_exact := payloadImage.ofVal_exact
  fits p := Canonical.fits p.val

end Effect4.Store
