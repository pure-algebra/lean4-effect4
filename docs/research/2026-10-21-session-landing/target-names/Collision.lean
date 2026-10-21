import Effect4.Api.Session
import Effect4.Api.Codegen
import Compiler.Code.Module
import TypeScript.Render

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
  let emission ← match session.typed.emit "main" with
    | .ok e => pure e
    | .error why => throw (IO.userError s!"emitter refused: {reprStr why}")
  IO.println "emitter accepted"
  let file ← match emission.file "./prelude/prelude.ts" with
    | .ok file => pure file
    | .error why => throw (IO.userError s!"file refused: {reprStr why}")
  IO.FS.writeFile "/tmp/effect4-session-target-review-20261021/session.ts" (TypeScript.Render.module TypeScript.house0 file)
  IO.println s!"free names: {reprStr (Codegen.freeNames file)}"
  match Api.readFile file session.table with
    | .ok p => IO.println s!"readFile accepted; equal program: {decide (p = session.program)}"
    | .error why => IO.println s!"readFile refused: {reprStr why}"
  match Api.admitModule "main" file session.table (Tools.Code.originsAt "./prelude/prelude.ts") [] session.table with
    | .ok p => IO.println s!"admitModule accepted; equal program: {decide (p.program = session.program)}"
    | .error _ => IO.println "admitModule refused"
