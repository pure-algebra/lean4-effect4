import Effect4.Api

/-!
# Red control for `VerifyRun.lean` (expected to FAIL: exit 1, two errors)

The claim it falsifies: "the run of an old program is unchanged by any row added to its table".
A row inserted in front makes the checked replay refuse the old journal and the raw run stop
short of the old exit.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.PedigreeVerify.RunRed

open Effect4 Effect4.Program Effect4.Machine

def row (name : String) (answer : Ty) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error := .never, cite := "" }

def oldTable : RowTable := [row "query" .nat]
def prepended : RowTable := [row "flag" .bool] ++ oldTable
def callZero : NativeEff := .perform (.external 0) (.lit (.nat 1))
def accepted : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 7))
def journal : List Api.Decision := [Api.evaluate, .answerAsync Api.root 0 accepted]

def refusal (table : RowTable) : Option Refusal :=
  match Api.replayChecked callZero 1000 journal [] table with
  | .inl _ => none
  | .inr (_, _, why, _) => some why

def exitOf (table : RowTable) : Option ExitV := (Api.run callZero 1000 [accepted] table).exit

-- Expected to fail: the checked replay of the old journal is refused after the insertion.
#guard refusal prepended = refusal oldTable
-- Expected to fail: the raw run no longer reaches the old exit.
#guard exitOf prepended = exitOf oldTable

end Research.PedigreeVerify.RunRed
