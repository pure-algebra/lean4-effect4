import Effect4.Laws.Program.Signature
import Effect4.Program.Admission

/-!
# `E4-TYPED-CE-041`: the API's admission is weaker than a lawful signature

`admitProgram` (`src/Effect4/Program/Admission.lean`) checks a row table's keys, kinds, columns
and formation. `LawfulSig` (`src/Effect4/Laws/Program/Signature.lean`) asks three things more, and
the typed state's milestones M5–M7 range over lawful sources only (`ProgramSource.lawful`):

1. every service key a row requires has a carrier (`served`);
2. every parameter a row's answer or error mentions is bound by its request (`wellScoped`);
3. no parameter sits under a union head (`templateAdmissible`).

So a program the API admits need not denote a lawful source. The bridge from admission to the
typed state takes the three as a premise (`AdmissionGap`, `lawfulSig_of_admitted`), until
decisions row 21's slice makes the signature's admission part of program admission.

The witnesses, one per clause, each admitted by the API and refused by `admitSig`. Kernel-checked.
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

/-- A row whose answer mentions a parameter its request does not bind (clause 2). -/
def unscopedRow : Row :=
  { name := "s", spelling := "S.s", kind := .async, request := .list (.var 0),
    answer := .list (.var 1), cite := "E4-TYPED-CE-041", registration := .external }

/-- A row with a parameter under a union head (clause 3). -/
def unionRow : Row :=
  { name := "u", spelling := "U.u", kind := .async, request := .union (.var 0) .nat, answer := .nat,
    cite := "E4-TYPED-CE-041", registration := .external }

/-- The API admits a program over each. -/
theorem admitted_unscoped :
    (admitProgram (.succeed (.lit .unit)) [unscopedRow]).toOption.isSome = true := by
  decide +kernel
theorem admitted_union :
    (admitProgram (.succeed (.lit .unit)) [unionRow]).toOption.isSome = true := by
  decide +kernel

/-- `admitSig` refuses each, at the row condition the API skipped. -/
theorem refused_unscoped :
    admitSig (SigApp.mk [unscopedRow] []) = .error (.row 0 .notWellScoped) := by
  decide +kernel
theorem refused_union :
    admitSig (SigApp.mk [unionRow] []) = .error (.row 0 (.templateNotAdmissible "request")) := by
  decide +kernel

/-- So the admitted program's table is no lawful source. -/
theorem not_lawful : ¬ LawfulSig (SigApp.mk [unservedRow] []) := fun h => by
  have hok := (admitSig_ok_iff _).mpr h
  rw [refused] at hok
  cases hok

end Test.Counterexamples.Program.AdmissionUnserved
