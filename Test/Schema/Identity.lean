import Effect4.Laws.Schema.Identity

/-! Readers and finite controls for deferred-key interpretation.
The capability is external to stored step data; malformed opaque values provide no such law.
These checks claim no allocation validity or abstract request-number equality. -/

set_option autoImplicit false

open Effect4.Store Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Schema Effect4.Schema.Model Effect4.Modules

namespace Test.Schema.Identity

-- The image reuses the existing handle image and rejects other roles and shapes.
#guard deferredKeyImage.toVal ⟨7⟩ == Effect4.Machine.Val.promise ⟨7⟩
#guard deferredKeyImage.ofVal (Effect4.Machine.Val.promise ⟨7⟩) == some ⟨7⟩
#guard deferredKeyImage.ofVal (.nat 7) == none
#guard deferredKeyImage.ofVal (.handle 2 7) == none

-- Equal and distinct keys compare through their deferred images.
#guard Model.deferredEqual Leaves.deferredKeys ⟨4⟩ ⟨4⟩
#guard !Model.deferredEqual Leaves.deferredKeys ⟨4⟩ ⟨9⟩
#guard nativeAtom "sameHandle"
  [deferredKeyImage.toVal ⟨4⟩, deferredKeyImage.toVal ⟨9⟩] == some (.bool false)

-- Malformed values receive a total answer without a reading claim.
#guard !Model.deferredEqual Leaves.opaque .unit .unit
#guard !Model.deferredEqual Leaves.opaque (.handle 2 4) (.handle 2 4)
#guard nativeAtom "sameHandle" [.unit, .unit] == none
#guard nativeAtom "sameHandle" [.handle 2 4, .handle 2 4] == some (.bool true)
-- Other roles remain opaque in the deferred-key interpretation.
#guard Leaves.deferredKeys.ref.2.toVal (.nat 7) == .nat 7
#guard Leaves.deferredKeys.var.2.toVal (.str "payload") == .str "payload"

-- Control: malformed raw values cannot meet the capability's image equation.
/-- error: Tactic `rfl` failed: The left-hand side
  Leaves.opaque.deferred.snd.toVal Val.unit
is not definitionally equal to the right-hand side
  Val.promise { index := 0 }

⊢ Leaves.opaque.deferred.snd.toVal Val.unit = Val.promise { index := 0 }
-/
#guard_msgs in
example : Leaves.opaque.deferred.2.toVal Effect4.Store.Val.unit = Effect4.Machine.Val.promise ⟨0⟩ := by
  rfl

end Test.Schema.Identity
