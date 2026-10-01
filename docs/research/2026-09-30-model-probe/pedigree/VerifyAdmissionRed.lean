import Effect4.Program.Admission
import Effect4.Codegen.Read

/-!
# Red control for `VerifyAdmission.lean` (expected to FAIL: exit 1, one error)

The claim it falsifies: "admission is conservative along any append that keeps the table lawful
by `LawfulTable`". A deferred row appended after the old program's row leaves the table lawful
and refuses the old program.
-/

set_option autoImplicit false

namespace Research.PedigreeVerify.AdmissionRed

open Effect4 Effect4.Program

def hostRow (name : String) (answer : Ty) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error := .never, cite := "" }

def oldTable : RowTable := [hostRow "query" .nat]
def deferredRow : Row := { hostRow "flag" .bool with registration := .deferred }
def appendedDeferred : RowTable := oldTable ++ [deferredRow]
def callZero : NativeEff := .perform (.external 0) (.lit (.nat 1))

def admitted (p : NativeEff) (table : RowTable) : Bool :=
  match admitProgram p table with
  | .ok _ => true
  | .error _ => false

-- Expected to fail: the append is lawful by names, and the old program is still refused.
#guard LawfulTable appendedDeferred → admitted callZero appendedDeferred

end Research.PedigreeVerify.AdmissionRed
