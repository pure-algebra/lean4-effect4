import Effect4.Program.Typing

/-!
# The computed whole-program typing result

Execution admission and checked code generation share this result of the existing
`typeOfProgram` checker. The program and signature are indices, so the recorded type
cannot belong to a different input. This package adds no typing algorithm, runner
restriction, target profile, or stored program representation.

The checker equations, uniqueness, and connection to the declarative judgment live
in `Laws/Program/CheckedTyping.lean`; the application graph does not import them.
-/

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

end Effect4.Program
