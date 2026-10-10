import Effect4.Program.Compile
import Effect4.Program.Authoring
import Effect4.Program.Definitions

/-! Finite scope controls. Placement: residual-program-typing / invocation-arm and
translation-simulation / proposed invoke-unfolds, serving R4/R7/R12.
No new theorem is proposed or proved here. The suspension observer covers only pure returns
and suspensions; it is not the scheduler, a host runner, or a general evaluator. -/
set_option autoImplicit false

namespace ContextScopeProbe
open Effect4 Effect4.Program Effect4.Program.Authoring

-- A raw Src builder can distinguish the placeholder's syntax from a real client.
def genericHole : Src NativeOp := fun _ _ => .ok (.perform (.param 0) (.lit .unit))
def realClient : Src NativeOp := fun _ _ => .ok (.succeed (.lit .unit))
def inspectBuilder (body : Src NativeOp) : Src NativeOp := fun env path => do
  let term ← body env path
  let n := match term with | .perform (.param 0) _ => 0 | _ => 1
  pure (.succeed (.lit (.nat n)))
#guard elaborate (inspectBuilder genericHole) = .ok (.succeed (.lit (.nat 0)))
#guard elaborate (inspectBuilder realClient) = .ok (.succeed (.lit (.nat 1)))
#guard (elaborate (inspectBuilder genericHole)).toOption !=
  (elaborate (inspectBuilder realClient)).toOption
#guard (Checker.checkModule (nativeSignature []) (.succeed (.lit (.nat 0)))).isOk
#guard (Checker.checkModule (nativeSignature []) (.succeed (.lit (.nat 1)))).isOk

-- The two-hop identity: invoke its definition, then invoke the passed program.
def identityDecl : DefDecl :=
  { name := "identityBody", request := .unit, answer := .nat,
    params := [{ name := "body", request := .unit, answer := .nat }] }
def identityRoot : NativeEff :=
  .defs [identityDecl]
    (.cons (.perform (.param 0) (.lit .unit)) .nil)
    (.invoke 0 (.lit .unit) (.cons (.succeed (.lit (.nat 7))) .nil))
#guard (Checker.checkModule (nativeSignature []) identityRoot).isOk

def point (fuel : Nat) : Point := { path := [1], env := [], fuel, tape := [] }
def pureAnswer (root : NativeEff) : Nat → NCode → Option Machine.Val
  | 0, _ => none
  | _ + 1, .success v => some v
  | n + 1, .suspend thunk => pureAnswer root n (suspendBodyAt root thunk)
  | _, _ => none

def callAnswer (fuel : Nat) : Option Machine.Val := pureAnswer identityRoot 12 (resolve identityRoot (point fuel))
def inlineAnswer (fuel : Nat) : Option Machine.Val :=
  pureAnswer identityRoot 12 (compileEff (.succeed (.lit (.nat 7))) (point fuel))
#guard inlineAnswer 1 = some (.nat 7)
#guard callAnswer 1 = none
#guard callAnswer 2 = none
#guard callAnswer 3 = some (.nat 7)
#guard callAnswer 4 = inlineAnswer 4

-- Checked nested forwarding keeps the caller's captured lexical value.
def forwardingDecl : DefDecl :=
  { identityDecl with name := "forward", request := .nat }
def lexicalRoot : NativeEff :=
  .defs [forwardingDecl, identityDecl]
    (.cons (.invoke 1 (.lit .unit) (.cons (.perform (.param 0) (.lit .unit)) .nil))
      (.cons (.perform (.param 0) (.lit .unit)) .nil))
    (.bind (.succeed (.lit (.nat 41)))
      (.invoke 0 (.lit (.nat 999)) (.cons (.succeed (.var 0)) .nil)))
#guard (Checker.checkModule (nativeSignature []) lexicalRoot).isOk
-- Observe the addressed call after the preceding pure bind has supplied its value.
def lexicalPoint : Point := { path := [1, 1], env := [.nat 41], fuel := 6, tape := [] }
#guard pureAnswer lexicalRoot 12 (resolve lexicalRoot lexicalPoint) = some (.nat 41)

-- A checked ordinary call can retain an inactive caller frame.
def ordinaryDecl : DefDecl :=
  { name := "ordinary", request := .unit, answer := .nat }
def ordinaryRoot : NativeEff :=
  .defs [identityDecl, ordinaryDecl]
    (.cons (.perform (.call 1) (.lit .unit))
      (.cons (.suspend (.succeed (.lit (.nat 7)))) .nil))
    (.invoke 0 (.lit .unit) (.cons (.succeed (.lit (.nat 42))) .nil))
#guard (Checker.checkModule (nativeSignature []) ordinaryRoot).isOk

def ordinaryBody : NCode :=
  match suspendBodyAt ordinaryRoot (.body (point 6)) with
  | .suspend thunk => suspendBodyAt ordinaryRoot thunk
  | other => other

def ordinaryFrameCount : Option Nat :=
  match ordinaryBody with
  | .suspend (.body p) => some p.params.length
  | _ => none
#guard ordinaryFrameCount = some 1
#guard pureAnswer ordinaryRoot 12 (resolve ordinaryRoot (point 6)) = some (.nat 7)

-- The checker still refuses absent parameters and an unbound program parameter.
#guard !(Checker.checkModule (nativeSignature [])
  (.defs [identityDecl] (.cons (.perform (.param 0) (.lit .unit)) .nil)
    (.invoke 0 (.lit .unit) .nil))).isOk
#guard !(Checker.check (nativeSignature []) [] [] (.perform (.param 0) (.lit .unit))).isOk

-- Smaller error columns can keep admission without keeping the inferred type equal.
def widerParam : ParamDecl :=
  { name := "body", request := .unit, answer := .nat, error := .string }
def declaredExit := Checker.check ((nativeSignature []).withParams [widerParam]) [] []
  (.exit (.perform (.param 0) (.lit .unit)))
def filledExit := Checker.check (nativeSignature []) [] []
  (.exit (.succeed (.lit (.nat 7))))
#guard widerParam.admits { answer := .nat, error := .never, requires := .empty }
#guard declaredExit.isOk
#guard filledExit.isOk
#guard (declaredExit.toOption.map (·.answer)) != (filledExit.toOption.map (·.answer))

end ContextScopeProbe

def main : IO Unit :=
  IO.println "PASS: raw builders can inspect holes; equal-fuel unfolding fails; nested forwarding keeps captures; smaller errors change inferred exit types; ordinary calls retain inactive frames; missing parameters are refused."
