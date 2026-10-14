import Effect4.Run
import Effect4.Api.Author
import Effect4.Program.Typing.Call

open Effect4 Effect4.Machine Effect4.Program

/- Review controls for rows-block-host, translation-simulation, R6.
   These finite checks serve the proposed call-instance admission connector.
   They make no claim about a whole program's agreement or scheduler progress. -/

def closedRow : Row :=
  { name := "closedUnion", spelling := "closedUnion", kind := .async,
    registration := .external, request := .unit, answer := .union .nat .nat,
    cite := "rows-block-host R6 version-5 review control" }

def closedProgram : NativeEff := .perform (.external 0) (.lit .unit)

#eval admitSig ⟨[closedRow], []⟩
#eval (admitProgram closedProgram ⟨[closedRow], []⟩).isOk
#eval (callAt (SigApp.signature ⟨[closedRow], []⟩) [] closedProgram []).map fun c =>
  (c.answer == closedRow.answer, c.answer == closedRow.answer.normalize, c.answer == .nat)

-- Instantiation traverses nominal type arguments even though membership does not.
def nominalWithVariable : Ty := .app "Foreign" [.var 0]
#eval nominalWithVariable.instantiate [(0, .nat)] == nominalWithVariable
#eval nominalWithVariable.instantiate [(0, .nat)] == .app "Foreign" [.nat]
