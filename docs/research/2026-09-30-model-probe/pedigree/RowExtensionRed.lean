import Effect4.Program.Authoring.Services

/-!
# Red control for the row-table half of `ServiceExtension.lean` (expected to FAIL: exit 1)

The claim it falsifies: "any row-table extension is conservative on old programs". Inserting a
row in front moves the old program's `external 0`, so the guard does not evaluate to `true`.
-/

set_option autoImplicit false

namespace Research.Pedigree.RowsRed

open Effect4 Effect4.Program

def hostRow (name : String) (answer : Ty) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error := .never, cite := "" }

def oldTable : RowTable := [hostRow "query" .nat]
def prepended : RowTable := [hostRow "flag" .bool] ++ oldTable
def callZero : NativeEff := .perform (.external 0) (.lit (.nat 1))

def answerOf (sig : Signature NativeOp) (p : NativeEff) : Option Ty :=
  (typeOf sig p).map EffTy.answer

-- Expected to fail: insertion in front is not conservative.
#guard answerOf (nativeSignature prepended) callZero == answerOf (nativeSignature oldTable) callZero

end Research.Pedigree.RowsRed
