import Effect4.Laws.Program.Typed.Admission
import Effect4.Laws.Program.Typed.Residual

/-! # Membership at a world, and the controls of the payload inversions (M3a) -/

set_option autoImplicit false

namespace Test.Program.TypedResidual

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects
open Effect4.Program.Typed

abbrev World := Effect4.Program.Typed.World

/-! ## Positive Witnesses -/

/-- Primitive booleans satisfy the membership judgment. -/
theorem test_fits_bool (w : World) : Fits w (Val.bool true) .bool := trivial

/-- A pure boolean exit uses the same value membership. -/
theorem test_fitsExit_bool (w : World) :
    FitsExit w (EffTy.pure .bool) (.success (Val.bool true)) := trivial

/-! ## Negative Controls / Falsifiers -/

/-- An undeclared cell is not live, even when heap contents are unconstrained. -/
theorem forged_cell_not_live (w : World) (hnone : w.Ρ ⟨0⟩ = none) :
    ¬ Live w (Val.cell ⟨0⟩) := by
  intro hlive
  have hlive0 := hlive (2, 0) List.mem_cons_self
  change (w.Ρ ⟨0⟩).isSome = true at hlive0
  rw [hnone] at hlive0
  cases hlive0

/-- An undeclared cell cannot fit a reference type. -/
theorem forged_cell_not_fit (w : World) (hnone : w.Ρ ⟨0⟩ = none) :
    ¬ Fits w (Val.cell ⟨0⟩) (Ty.refOf .bool) := by
  rintro ⟨ty, hsome, _⟩
  rw [hnone] at hsome
  cases hsome

/-- A fiber id absent from Γ cannot fit a fiber type. -/
theorem forged_fiber_not_fit (w : World) (id : FiberId) (hnone : w.Γ id = none) :
    ¬ Fits w (Val.fiber id) (Ty.fiberOf .bool .unit) := by
  rintro ⟨fty, hsome, _⟩
  rw [hnone] at hsome
  cases hsome

/-- Negative control: `unguard` payload inversion rejects unadmitted payloads. -/
theorem unguard_inversion_rejects_unadmitted (root : NativeEff) (w : World) (ex : ExitV)
    (k : ExitV → RProgram)
    (hadmit : TypedProg root w (EffTy.pure (Ty.refOf .bool)) (.vis (.inr (.unguard ex)) k))
    (hex : ex = .success (Val.cell ⟨0⟩))
    (hnone : w.Ρ ⟨0⟩ = none) : False := by
  have hstrong := unguard_payload_inv root w (EffTy.pure (Ty.refOf .bool)) ex k hadmit
  rw [hex] at hstrong
  exact forged_cell_not_fit w hnone hstrong.1

/-- Negative control: `finishFinalizer` payload inversion rejects unadmitted payloads. -/
theorem finishFinalizer_inversion_rejects_unadmitted (root : NativeEff) (w : World) (ex : ExitV)
    (k : ExitV → RProgram)
    (hadmit : TypedProg root w (EffTy.pure (Ty.refOf .bool)) (.vis (.inr (.finishFinalizer ex)) k))
    (hex : ex = .success (Val.cell ⟨0⟩))
    (hnone : w.Ρ ⟨0⟩ = none) : False := by
  have hstrong := finishFinalizer_payload_inv root w (EffTy.pure (Ty.refOf .bool)) ex k hadmit
  rw [hex] at hstrong
  exact forged_cell_not_fit w hnone hstrong.1

end Test.Program.TypedResidual
