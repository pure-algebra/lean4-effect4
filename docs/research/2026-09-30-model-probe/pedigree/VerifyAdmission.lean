import Effect4.Program.Admission
import Effect4.Codegen.Read

/-!
# Pedigree verifier probe (2026-09-30): admission along a table append (C3 at admission, C6)

Finite checks (tested, not proved). The seat's C6 states lawfulness of an extension as local,
citing `LawfulTable` (`src/Effect4/Codegen/Read.lean:1943`: unique keys, no built-in collision,
no dropped trailing names, safe names). Admission asks more of the whole table
(`AdmittedProgram`, `src/Effect4/Program/Admission.lean:89-95`): every row registrable
(`checkTable`, `src/Effect4/Program/Native.lean:347-354`) and no row mentioning the reserved
integer type (`findIntInTable`). So an appended row that the old program never calls, lawful by
names, still makes the old program inadmissible: admission is conservative along an append only
when the new rows pass the runner's own checks too.
-/

set_option autoImplicit false

namespace Research.PedigreeVerify.Admission

open Effect4 Effect4.Program

def hostRow (name : String) (answer : Ty) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error := .never, cite := "" }

def oldTable : RowTable := [hostRow "query" .nat]

/-- A row the oracle does not answer: lawful by names, not registrable by this runner. -/
def deferredRow : Row := { hostRow "flag" .bool with registration := .deferred }

/-- A row whose answer is the reserved integer type. -/
def intRow : Row := hostRow "count" .int

def appendedGood : RowTable := oldTable ++ [hostRow "flag" .bool]
def appendedDeferred : RowTable := oldTable ++ [deferredRow]
def appendedInt : RowTable := oldTable ++ [intRow]

/-- An old program: it calls row 0 only. -/
def callZero : NativeEff := .perform (.external 0) (.lit (.nat 1))

def admitError (p : NativeEff) (table : RowTable) : Option AdmitRefusal :=
  match admitProgram p table with
  | .ok _ => none
  | .error e => some e

def uninhabited? : Option AdmitRefusal → Bool
  | some (.uninhabited _) => true
  | _ => false

-- The old program is admitted against its table and against a registrable append.
#guard admitError callZero oldTable = none
#guard admitError callZero appendedGood = none

-- Both bad appends are lawful by names (the seat's C6 test) ...
#guard LawfulTable appendedDeferred
#guard LawfulTable appendedInt

-- ... and each makes the old program inadmissible, though it never calls the new row.
#guard admitError callZero appendedDeferred = some (.table (.notExternal 1))
#guard uninhabited? (admitError callZero appendedInt)

-- The checker alone is conservative on the old program for all three appends (C3 holds).
#guard (typeOf (nativeSignature appendedDeferred) callZero) = (typeOf (nativeSignature oldTable) callZero)
#guard (typeOf (nativeSignature appendedInt) callZero) = (typeOf (nativeSignature oldTable) callZero)

end Research.PedigreeVerify.Admission
