import Effect4.Laws.Program.Signature
import Effect4.Program.Admission

/-!
# `E4-TYPED-CE-041`: the API's admission is weaker than a lawful signature

`admitProgram` (`src/Effect4/Program/Admission.lean`) checks a row table's keys, kinds, columns
and formation. It does not check that every service key a row requires has a carrier. The
`served` clause of `LawfulSig` (`src/Effect4/Laws/Program/Signature.lean`) does, and the typed
state's milestones M5–M7 range over lawful sources only (`ProgramSource.lawful`). So a program the
API admits need not denote a lawful source: the bridge from admission to the typed state takes the
served premise (`Effect4.Program.Typed.lawfulSig_of_admitted`), until decisions row 21's slice
makes the signature's admission part of program admission.

The witness: one host row that requires the key at service code 30, which no built-in carrier
serves, and a program that performs that row. Kernel-checked.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Program.AdmissionUnserved

open Effect4 Effect4.Program

/-- An application service key at a code no built-in carrier serves. -/
def appKey : ServiceKey := ⟨⟨30⟩, ⟨30⟩⟩

/-- A host row that requires `appKey`. -/
def unservedRow : Row :=
  { name := "a", spelling := "A.a", kind := .async, request := .unit, answer := .nat,
    cite := "E4-TYPED-CE-041", registration := .external, requires := [appKey] }

/-- `yield* A.a()`: the program performs the row. -/
def callIt : NativeEff := .perform (.external 0) (.lit .unit)

/-- The API admits the program over the table. -/
theorem admitted : (admitProgram callIt [unservedRow]).toOption.isSome = true := by
  decide +kernel

/-- The signature of the same table is not lawful: the row's key has no carrier. -/
theorem refused : admitSig (SigApp.mk [unservedRow] []) = .error (.unservedKey 0 appKey) := by
  decide +kernel

/-- So the admitted program's table is no lawful source. -/
theorem not_lawful : ¬ LawfulSig (SigApp.mk [unservedRow] []) := fun h => by
  have hok := (admitSig_ok_iff _).mpr h
  rw [refused] at hok
  cases hok

end Test.Counterexamples.Program.AdmissionUnserved
