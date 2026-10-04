import Effect4.Laws.Program.Signature
import Effect4.Program.Admission

/-!
# `E4-TYPED-CE-041`: the API's admission was weaker than a lawful signature (repaired)

Until decisions row 21's slice, step 2, `admitProgram` (`src/Effect4/Program/Admission.lean`)
checked a row table's keys, kinds, columns and formation, and skipped three conditions of
`LawfulSig` (`src/Effect4/Laws/Program/Signature.lean`), over which the typed state's milestones
M5–M7 range (`ProgramSource.lawful`):

1. every service key a row requires has a carrier (`served`);
2. every parameter a row's answer or error mentions is bound by its request (`wellScoped`);
3. no parameter sits under a union head (`templateAdmissible`).

So a program the API admitted need not denote a lawful source, and the bridge to the typed state
took the three as a premise. Admission now runs the signature's located refusal (`admitSig`,
`src/Effect4/Program/SigApp.lean`), so it refuses each witness with the refusal `admitSig` gives,
and the bridge (`lawfulSig_of_admitted`) has no premise.

The witnesses, one per clause, each refused by `admitProgram` at the clause `admitSig` names.
Kernel-checked (`decide +kernel`). The red controls below are the attack: the old acceptance of
each witness, evaluated, no longer holds.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Program.AdmissionUnserved

open Effect4 Effect4.Program

/-- The refusal of an admission, `none` when it admits. -/
def refusalOf {α : Type} : Except AdmitRefusal α → Option AdmitRefusal
  | .error why => some why
  | .ok _ => none

/-- An application service key at a code no built-in carrier serves. -/
def appKey : ServiceKey := ⟨⟨30⟩, ⟨30⟩⟩

/-- A host row that requires `appKey`. -/
def unservedRow : Row :=
  { name := "a", spelling := "A.a", kind := .async, request := .unit, answer := .nat,
    cite := "E4-TYPED-CE-041", registration := .external, requires := [appKey] }

/-- `yield* A.a()`: the program performs the row. -/
def callIt : NativeEff := .perform (.external 0) (.lit .unit)

/-- A row whose answer mentions a parameter its request does not bind (clause 2). -/
def unscopedRow : Row :=
  { name := "s", spelling := "S.s", kind := .async, request := .list (.var 0),
    answer := .list (.var 1), cite := "E4-TYPED-CE-041", registration := .external }

/-- A row with a parameter under a union head (clause 3). -/
def unionRow : Row :=
  { name := "u", spelling := "U.u", kind := .async, request := .union (.var 0) .nat, answer := .nat,
    cite := "E4-TYPED-CE-041", registration := .external }

/-- Clause 1: the API refuses the program, at the required key with no carrier. -/
theorem refused :
    refusalOf (admitProgram callIt ⟨[unservedRow], []⟩) =
      some (.signature (.unservedKey 0 appKey)) := by
  decide +kernel

/-- Clause 2: the API refuses a program over the row that does not bind its answer's parameter. -/
theorem refused_unscoped :
    refusalOf (admitProgram (.succeed (.lit .unit)) ⟨[unscopedRow], []⟩) =
      some (.signature (.row 0 .notWellScoped)) := by
  decide +kernel

/-- Clause 3: the API refuses a program over the row with a parameter under a union head. -/
theorem refused_union :
    refusalOf (admitProgram (.succeed (.lit .unit)) ⟨[unionRow], []⟩) =
      some (.signature (.row 0 (.templateNotAdmissible "request"))) := by
  decide +kernel

/-- The table of clause 1 is no lawful source, which is why admission refuses it. -/
theorem not_lawful : ¬ LawfulSig (SigApp.mk [unservedRow] []) := fun h => by
  have hok := (admitSig_ok_iff _).mpr h
  have hrefused : admitSig (SigApp.mk [unservedRow] []) = .error (.unservedKey 0 appKey) := by
    decide +kernel
  rw [hrefused] at hok
  cases hok

/-! ## Red controls: the attack's acceptance no longer holds

Each is the old acceptance of a witness, which `admitProgram` gave before the repair. -/

/-- RED, clause 1: the program over the row whose required key has no carrier is admitted. -/
def red_unserved : Bool := (admitProgram callIt ⟨[unservedRow], []⟩).toOption.isSome
/--
error: Expression
  red_unserved
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_unserved

/-- RED, clause 2: a program over the row that does not bind its answer's parameter is admitted. -/
def red_unscoped : Bool :=
  (admitProgram (.succeed (.lit .unit)) ⟨[unscopedRow], []⟩).toOption.isSome
/--
error: Expression
  red_unscoped
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_unscoped

/-- RED, clause 3: a program over the row with a parameter under a union head is admitted. -/
def red_union : Bool := (admitProgram (.succeed (.lit .unit)) ⟨[unionRow], []⟩).toOption.isSome
/--
error: Expression
  red_union
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_union

end Test.Counterexamples.Program.AdmissionUnserved
