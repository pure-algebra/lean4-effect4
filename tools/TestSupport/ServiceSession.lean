import Compiler.Code.Module
import Compiler.Json
import Test.Api.SessionFixtures

/-! Finite target evidence for the checked service-session constructor.
The driver prints the actual constructed program and records the Lean run's typed replies.
The service-identity gate compares them with pinned Effect execution through tsgo 7.
This is no general compiler, service-behaviour, or transport-support theorem. -/

set_option autoImplicit false
namespace TestSupport.ServiceSession
open Effect4 Effect4.Program Effect4.Machine

/-- Encode actual fixture observations through the existing typed value codec. -/
def encoded (ty : Ty) (value : Val) : IO NatJson :=
  match Ty.encode [] ty value with
  | some json => pure (NatJson.ofBinary64 (Schema.Codec.normJ json))
  | none => throw (IO.userError "service session: observation does not encode")

/-- Emit the constructed session and its Lean observations through the existing owners. -/
def emit (out : System.FilePath) : IO Unit := do
  let some built := Test.Api.SessionFixtures.exampleSession
    | throw (IO.userError "service session: construction refused")
  let emission ← match built.typed.emit "sessionProgram" with
    | .ok emission => pure emission
    | .error _ => throw (IO.userError "service session: target emission refused")
  let root ← IO.currentDir
  let file ← match emission.file (root / "ts/prelude/prelude.ts").toString ["Session"] with
    | .ok file => pure file
    | .error _ => throw (IO.userError "service session: file emission refused")
  let file := { file with imports := file.imports ++
    [.named [{ imported := "Session", localName := "Session", typeOnly := false }]
      "./session-host.ts" false] }
  IO.FS.writeFile (out / "session.ts") (Tools.Code.moduleText Tools.Code.Ts.width file)
  let some (run, _) := Test.Api.SessionFixtures.exampleRun
    | throw (IO.userError "service session: Lean execution unavailable")
  let some exit := run.exit
    | throw (IO.userError "service session: Lean execution has no final exit")
  let requests ← Test.Api.SessionFixtures.exampleRequests.mapM
    (encoded (.prod (.lit "check") .nat))
  let replies ← (Test.Api.SessionFixtures.replies run).mapM fun (_, reply) => encoded (.exitOf .nat .nat) reply
  let final ← encoded (.exitOf .unit .never) (reifyExitVal exit)
  IO.FS.writeFile (out / "session-expected.json") (Compiler.jsonText (.obj
    [("requests", .arr requests), ("replies", .arr replies), ("exit", final)]) ++ "\n")

end TestSupport.ServiceSession
