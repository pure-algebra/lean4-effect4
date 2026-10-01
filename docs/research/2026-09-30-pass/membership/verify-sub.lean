import Effect4.Laws.Program.Typed.Admission

/-!
# Verifier probe: the "mutual subtypes" claim behind G7

Adversarial verifier of seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. The seat proves
`Ty.sub (refOf nat) (refOf (union nat nat)) = true` (`Gaps.lean:377`) and calls the two types
mutual subtypes. The reverse direction, checked here by kernel evaluation, and the red control:
a genuinely different cell type is not a subtype.
-/

set_option autoImplicit false

namespace Research.Pass.Membership.VerifySub
open Effect4 Effect4.Program

theorem sub_ref_forward : Ty.sub (.refOf .nat) (.refOf (.union .nat .nat)) = true := by
  decide +kernel

theorem sub_ref_backward : Ty.sub (.refOf (.union .nat .nat)) (.refOf .nat) = true := by
  decide +kernel

/-- Red control: `refOf nat` is not below `refOf bool`. -/
theorem sub_ref_control : Ty.sub (.refOf .nat) (.refOf .bool) = false := by
  decide +kernel

#print axioms sub_ref_forward
#print axioms sub_ref_backward
#print axioms sub_ref_control

end Research.Pass.Membership.VerifySub
