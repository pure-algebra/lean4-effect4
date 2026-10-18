module

public import Effect4.Program.Typing

/-!
# The computed whole-program typing result

Execution admission and checked code generation share this result of the existing
`typeOfProgram` checker. The program and signature are indices, so the recorded type
cannot belong to a different input. This package adds no typing algorithm, runner
restriction, target profile, or stored program representation.

Where the checker refuses, `programRefusal` locates its refusal: an ill-formed layer reference at
its site, else the module check's refusal of the expansion. It is absent exactly when the program
types (`programRefusal_none_iff`), the whole-program typing's own law. `programTyping` is the
certificate or that refusal; admission reports the refusal (`AdmitRefusal.illTyped`), and
`Api.explain` is the same refusal at an application's signature.

The checker equations, uniqueness, and connection to the declarative judgment live
in `Laws/Program/CheckedTyping.lean`; the application graph does not import them.
-/

@[expose] public section

namespace Effect4.Program

/-- The type computed for this exact program and signature. Reference validation and
expansion are the existing whole-program checker's, not an execution rewrite. -/
structure TypedProgram (sig : Signature Op) (program : Eff Op) where
  ty : EffTy
  typed : typeOfProgram sig program = some ty

/-- Retain the successful result of the one whole-program checker as computed evidence.
The failure result is exactly that checker's `none`. -/
def checkTypedProgram (sig : Signature Op) (program : Eff Op) :
    Option (TypedProgram sig program) :=
  match h : typeOfProgram sig program with
  | none => none
  | some ty => some ⟨ty, h⟩

/-- **The whole program's located refusal** (DI-86): an ill-formed layer reference at its site,
the first in program order (`Eff.firstRefFault`, decisions row 341), else the module check's
refusal of the expansion (`Checker.checkModule`, decisions row 328). `none` exactly when
`typeOfProgram` answers (`programRefusal_none_iff`). -/
def programRefusal {Op : Type} (sig : Signature Op) (program : Eff Op) : Option TypeRefusal :=
  match program.firstRefFault with
  | some (site, target, why) => some ⟨site, .referenceIllFormed target why⟩
  | none => Checker.refusal (Checker.checkModule sig program.expandRefs)

/-- **The refusal is absent exactly when the program types.** Both sides test the references'
formation (`Eff.firstRefFault_eq_none`); where it holds, both read the one module check of the
expansion, and where it fails, the refusal names the reference and the program has no type. -/
theorem programRefusal_none_iff {Op : Type} (sig : Signature Op) (program : Eff Op) :
    programRefusal sig program = none ↔ (typeOfProgram sig program).isSome = true := by
  unfold programRefusal typeOfProgram
  cases h : program.firstRefFault with
  | none =>
    rw [if_pos ((Eff.firstRefFault_eq_none program).mp h)]
    show Checker.refusal _ = none ↔ Option.isSome (Except.toOption _) = true
    cases Checker.checkModule sig program.expandRefs with
    | ok _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | error _ => exact ⟨nofun, nofun⟩
  | some f =>
    obtain ⟨site, target, why⟩ := f
    have hwf : program.layerRefsWF = false := by
      cases hw : program.layerRefsWF with
      | false => rfl
      | true =>
        rw [(Eff.firstRefFault_eq_none program).mpr hw] at h
        cases h
    rw [hwf]
    exact ⟨nofun, nofun⟩

/-- A program the checker refuses has a located refusal: the premise `programTyping` reads its
refusal under. -/
theorem programRefusal_isSome {Op : Type} {sig : Signature Op} {program : Eff Op}
    (h : checkTypedProgram sig program = none) : (programRefusal sig program).isSome = true := by
  cases hr : programRefusal sig program with
  | some _ => rfl
  | none =>
    have hty := (programRefusal_none_iff sig program).mp hr
    unfold checkTypedProgram at h
    split at h
    · rename_i hnone
      rw [hnone] at hty
      cases hty
    · cases h

/-- **The whole-program typing, refused with its located reason**: the certificate where the
checker answers, and its located refusal where it refuses (`programRefusal`). Admission reports
the refusal (`AdmitRefusal.illTyped`). -/
def programTyping {Op : Type} (sig : Signature Op) (program : Eff Op) :
    Except TypeRefusal (TypedProgram sig program) :=
  match h : checkTypedProgram sig program with
  | some typed => .ok typed
  | none => .error ((programRefusal sig program).get (programRefusal_isSome h))

end Effect4.Program
