module

public import Effect4.Schema.Modeled
public import Effect4.Machine.Alphabets

/-!
# Schema.Identity — an interpretation of deferred identities

A deferred-key image reuses the runtime's promise handle image.
`Leaves.deferredKeys` replaces only the deferred leaf of the opaque interpretation.
`DeferredIdentity` is an interpretation capability, outside stored step syntax.
Its key projection and image equation justify comparison of deferred keys.
It establishes no allocation validity, membership, or equality of abstract request numbers.
The consumer is the deferred comparison arm of `step-language-sound`, requirement R10.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Schema
open Effect4.Store Effect4.Machine Model

/-- A deferred key's exact image: the promise handle with that key's index. -/
def deferredKeyImage : Image DeferredKey :=
  (HandleKind.handleOf .promise).equiv DeferredKey.mk DeferredKey.index
    (fun _ => rfl) (fun _ => rfl)

/-- The deferred-key interpretation; all other leaves retain their opaque carriers. -/
def Model.Leaves.deferredKeys : Leaves :=
  { Leaves.opaque with deferred := ⟨DeferredKey, deferredKeyImage⟩ }

/-- An interpretation whose deferred values encode deferred keys.
This capability is external to the step's first-order data. -/
structure DeferredIdentity (L : Leaves) where
  key : L.deferred.1 → DeferredKey
  image_eq : ∀ x, L.deferred.2.toVal x = Machine.Val.promise (key x)

/-- Read only a promise handle's key; every other value shape refuses. -/
def Model.deferredKeyOf (value : Store.Val) : Option DeferredKey :=
  (HandleKind.ofHandle .promise value).map DeferredKey.mk

/-- A total comparison of extracted promise keys. Malformed values answer false.
Only an interpretation capability supplies a reading law for this candidate. -/
def Model.deferredEqual (L : Leaves) (a b : L.deferred.1) : Bool :=
  match Model.deferredKeyOf (L.deferred.2.toVal a), Model.deferredKeyOf (L.deferred.2.toVal b) with
  | some ka, some kb => decide (ka = kb)
  | _, _ => false

namespace DeferredIdentity

/-- Compare the keys; do not compare arbitrary value trees. -/
def equal {L : Leaves} (I : DeferredIdentity L) (a b : L.deferred.1) : Bool :=
  decide (I.key a = I.key b)

/-- The deferred-key interpretation supplies the capability without further premises. -/
def deferredKeys : DeferredIdentity Leaves.deferredKeys where
  key := id
  image_eq _ := rfl

end DeferredIdentity
end Effect4.Schema
