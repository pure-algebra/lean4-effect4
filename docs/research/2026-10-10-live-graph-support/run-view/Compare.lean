import Baseline
import Tools.View.Run
import Effect4.Store.Domain.ProgramWire

open Effect4 Effect4.Program Tools.View
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

-- Complete page output, including code, line states, fiber graph and pagination.
#guard Effect4.Program.Wire.Corpus.all.all fun (name, p) =>
  reprStr (Tools.View.Run.frames name p 32) == reprStr (RunViewBaseline.frames name p 32)

-- A nonempty table changes the checked source type and emitted host spelling.
def hostRow : Row :=
  { name := "read", spelling := "Host.read", shape := .call, kind := .async,
    registration := .external, request := .nat, answer := .nat, cite := "render control" }
def hostProgram : NativeEff := .perform (.external 0) (.lit (.nat 3))
#guard (Api.Author.Internal.finishBuild hostProgram [hostRow] [("read", 0)]).isOk
#guard match Api.Author.Internal.finishBuild hostProgram [hostRow] [("read", 0)] with
  | .error _ => false
  | .ok b =>
    let s := Effect4.Run.open b "view"
    let current := Tools.View.Run.frame "host" none s "open"
    let former := RunViewBaseline.frame "host" hostProgram none s "open"
    current.lines.any (fun line => line.type == "number" && line.state != .refused) &&
      former.lines.any (fun line => line.state == .refused) &&
      match current.code with
      | none => false
      | some code => code.lines.any (·.contains "Host.read") &&
          !code.lines.any (·.startsWith "no module:")

-- Both paths reach the same live host-call frontier and retain their static code.
#guard match Api.Author.Internal.finishBuild hostProgram [hostRow] [("read", 0)] with
  | .error _ => false
  | .ok b =>
    let ps := Tools.View.Run.framesBuilt "host" b 32
    ps.length > 1 && ps.all fun p => reprStr p.code == reprStr (Tools.View.Run.prepare b).code
