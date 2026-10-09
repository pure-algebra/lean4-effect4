import Effect4.Laws.Modules.Step
open Effect4.Program Effect4.Store Effect4.Schema Effect4.Schema.Model Effect4.Modules
namespace OW02Safety
-- Opaque identities have an exact value image, not a membership guarantee.
def identityStep : Step [.deferredOf .unit .never] (.deferredOf .unit .never) :=
  .var (.here _ _)
#guard identityStep.canonical && identityStep.normal
#guard (imageAt Leaves.opaque (.deferredOf .unit .never)).toVal
  (identityStep.eval (Γ := [.deferredOf .unit .never]) Leaves.opaque (Val.nat 7, ())) == Val.nat 7
#guard !Val.hasTy ((imageAt Leaves.opaque (.deferredOf .unit .never)).toVal
  (identityStep.eval (Γ := [.deferredOf .unit .never]) Leaves.opaque (Val.nat 7, ()))) (.deferredOf .unit .never) []
-- Duplicate names are rejected by both field-operation checks.
def duplicate : Step [.record [("x", false, .nat), ("x", false, .nat)]] .nat :=
  .get (.var (.here _ _)) (.there _ _ _ (.here _ _ _))
#guard !duplicate.canonical && !duplicate.normal
-- A certificate is sufficient, not a complete normality test.
#guard !Ty.certNormal (.union .nat .bool)
-- Normal types need not have inhabitants in the carrier profile.
#guard Ty.certNormal .int
-- A frame statement needs an update spine even when the expression writes nothing.
def copied : Step [.record [("x", false, .nat)]]
    (.record [("x", false, .nat)]) := .fst (.pair (.var (.here _ _)) (.unit))
#guard copied.writes.isEmpty && copied.spine == none
end OW02Safety
