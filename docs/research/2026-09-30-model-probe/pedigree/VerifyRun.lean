import Effect4.Api

/-!
# Pedigree verifier probe (2026-09-30): the run of an old program along a table append

Finite checks (tested, not proved). For host rows the tree has no free-monad meaning yet (DI-69
is ruled and unimplemented: no `RowSig`, no `denoteRows`), so the package's C2 lemmas
(`interpret_inl`) have no instance for a host row. What an old program's host call means today is
the native machine's run, against the table supplied beside the program (`Api.replay`,
`src/Effect4/Api.lean:285-293`). This checks the operational form of C2 on one old program:

- appending a row leaves the raw run and the checked replay of the old journal unchanged;
- inserting the row in front makes the checked replay refuse the old journal at the new row's
  type, and the raw run with the old preloaded answer no longer finishes: it stops at a live
  frontier waiting for the host.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Research.PedigreeVerify.Run

open Effect4 Effect4.Program Effect4.Machine

def row (name : String) (answer : Ty) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error := .never, cite := "" }

def oldTable : RowTable := [row "query" .nat]
def appended : RowTable := oldTable ++ [row "flag" .bool]
def prepended : RowTable := [row "flag" .bool] ++ oldTable

/-- An old program: it calls row 0 once. -/
def callZero : NativeEff := .perform (.external 0) (.lit (.nat 1))

def accepted : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 7))

/-- The old journal: evaluate, then the host answers the root's park with `7`. -/
def journal : List Api.Decision := [Api.evaluate, .answerAsync Api.root 0 accepted]

def refusal (table : RowTable) : Option Refusal :=
  match Api.replayChecked callZero 1000 journal [] table with
  | .inl _ => none
  | .inr (_, _, why, _) => some why

def exitOf (table : RowTable) : Option ExitV := (Api.run callZero 1000 [accepted] table).exit

-- The old program, its table: the checked journal is accepted and the run exits with 7.
#guard refusal oldTable = none
#guard exitOf oldTable = some (.success (.nat 7))

-- Append: the same.
#guard refusal appended = none
#guard exitOf appended = exitOf oldTable

-- Insert in front: the call is retyped, the checked replay refuses the old journal at the new
-- row's type ...
#guard Api.typeOf callZero prepended = some (.pure .bool)
#guard refusal prepended = some (.answerType Api.root 0 .bool)
-- ... and the raw run with the old preloaded answer no longer finishes: a live frontier with
-- no exit, waiting for the host.
#guard (Api.run callZero 1000 [accepted] prepended).outcome = Api.Outcome.frontier
#guard exitOf prepended = none

end Research.PedigreeVerify.Run
