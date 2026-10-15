import Effect4.Author
import Effect4.Machine.Record
import Effect4.Machine.Alphabets

namespace Test.Dogfood

open Effect4.Program Effect4.Program.Authoring


/-- A record value, its fields in canonical order. -/
def recordOf (names : List String) (values : List Effect4.Machine.Val) : Effect4.Machine.Val :=
  (Effect4.Machine.Record.build names values).getD .unit


/-- A module whose only field is its main program. -/
def program (src : Src NativeOp) : Module NativeOp := { main := src }

end Test.Dogfood
