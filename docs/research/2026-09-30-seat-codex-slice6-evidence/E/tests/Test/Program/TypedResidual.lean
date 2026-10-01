import Effect4.Laws.Program.Typed.Admission
import Effect4.Laws.Program.Typed.Residual

/-! # Tests for M3a Foundations: Admission, Protocols, Residual Typing, and Settling Cases -/

set_option autoImplicit false

namespace Test.Program.TypedResidual

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects
open Effect4.Program.Typed

abbrev World := Effect4.Program.Typed.World

/-! ## Positive Witnesses -/

/-- Settling Case 1: polymorphic ref allocation followed by read types in a heterogeneous heap. -/
theorem test_settling_ref_allocation (root : NativeEff) (w : World) (h0 : HeapTypedAt w ⟨0⟩ .nat) :
    TypedProg root w (EffTy.pure .bool) refAllocGetProg :=
  settling_ref_allocation root w h0

/-- Settling Case 1 preservation: allocating a new boolean ref preserves existing nat ref types. -/
theorem test_settling_ref_preserves_nat (w w' : World) (ordered : w.leHost w') (h0 : HeapTypedAt w ⟨0⟩ .nat) :
    HeapTypedAt w' ⟨0⟩ .nat :=
  settling_ref_preserves_nat w w' ordered h0

/-- Settling Case 2: addressed fork admitting child body returns a typed fiber handle. -/
theorem test_settling_fork (root : NativeEff) (w : World) (child : Body) (cert : EffTy)
    (hbody : BodyTyped root w child cert) :
    TypedProg root w (EffTy.pure (.fiberOf cert.answer cert.error)) (forkProg child) :=
  settling_fork root w child cert hbody

/-- Settling Case 2: addressed mask admitting body preserves its certificate type. -/
theorem test_settling_mask (root : NativeEff) (w : World) (flag : Bool) (body : Body) (cert : EffTy)
    (hbody : BodyTyped root w body cert) :
    TypedProg root w cert (maskProg flag body) :=
  settling_mask root w flag body cert hbody

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
  have hmem : Handle.cell ⟨0⟩ ∈ (Val.cell ⟨0⟩).keys := by
    rw [Val.keys_cell]
    exact List.mem_singleton_self _
  have hlive0 := hlive (Handle.cell ⟨0⟩) hmem
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
  exact forged_cell_not_fit w hnone hstrong

/-- Negative control: `finishFinalizer` payload inversion rejects unadmitted payloads. -/
theorem finishFinalizer_inversion_rejects_unadmitted (root : NativeEff) (w : World) (ex : ExitV)
    (k : ExitV → RProgram)
    (hadmit : TypedProg root w (EffTy.pure (Ty.refOf .bool)) (.vis (.inr (.finishFinalizer ex)) k))
    (hex : ex = .success (Val.cell ⟨0⟩))
    (hnone : w.Ρ ⟨0⟩ = none) : False := by
  have hstrong := finishFinalizer_payload_inv root w (EffTy.pure (Ty.refOf .bool)) ex k hadmit
  rw [hex] at hstrong
  exact forged_cell_not_fit w hnone hstrong

#print axioms test_settling_ref_allocation
#print axioms test_settling_ref_preserves_nat
#print axioms test_settling_fork
#print axioms test_settling_mask
#print axioms forged_cell_not_live
#print axioms forged_cell_not_fit
#print axioms forged_fiber_not_fit
#print axioms unguard_inversion_rejects_unadmitted
#print axioms finishFinalizer_inversion_rejects_unadmitted

end Test.Program.TypedResidual
