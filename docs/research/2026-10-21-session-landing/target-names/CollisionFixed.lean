import Effect4.Api.Session
import Effect4.Api.Codegen

open Effect4 Effect4.Program
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def source : NativeEff :=
  .defs
    [{ name := "sessionMake", request := .unit, answer := .nat, role := .serviceInit "Session" },
     { name := "sessionRead", request := .nat, answer := .nat, role := .serviceMethod "Session" "read" 0 }]
    (.cons (.succeed (.lit (.nat 5))) (.cons (.succeed (.var 0)) .nil))
    (.succeed (.lit .unit)) .nil

#eval do
  let source ← match Api.Built.ofProgram {} source with
    | .ok b => pure b
    | .error _ => throw (IO.userError "source admission refused")
  let session ← match source.session "Session" with
    | .ok b => pure b
    | .error _ => throw (IO.userError "session constructor refused")
  IO.println "source and session admitted"
  match session.typed.emit "main" with
    | .error (.print (.unsafeName "Session")) =>
      IO.println "PASS: emitter refuses the captured Session namespace"
    | .error _ => throw (IO.userError "unexpected emission refusal")
    | .ok _ => throw (IO.userError "emitter accepted the captured Session namespace")
