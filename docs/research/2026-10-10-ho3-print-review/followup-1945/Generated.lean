import Effect4.Api
import Lean

/-! Finite generated-output controls. PLAN.md states the placement. -/
set_option autoImplicit false
namespace HO3GeneratedFollowup
open Effect4 Effect4.Program

def q (name : String) : ParamDecl := { name, request := .nat, answer := .nat }
def plainDef : DefDecl :=
  { name := "applyProgram", request := .nat, answer := .nat, params := [q "use"] }
def plain : NativeEff := .defs [plainDef]
  (.cons (.perform (.param 0) (.var 0)) .nil) (.succeed (.lit (.nat 1))) .nil

def payloadFields : List (String × Bool × Ty) := [("_tag", false, .lit "Payload"), ("id", false, .nat)]
def payloadBody : NativeEff := .succeed
  (.record payloadFields ["_tag", "id"]
    (.cons (.lit (.str "Payload")) (.cons (.lit (.nat 7)) .nil)))
def payload (param : String) : NativeEff :=
  .defs [{ name := "buildPayload", request := .nat, answer := .record payloadFields, params := [q param] }]
    (.cons payloadBody .nil) (.succeed (.lit (.nat 1))) .nil

def externalRow (qualified : Bool) : Row :=
  { name := "widgetRead", spelling := if qualified then "Widget.run" else "readWidget",
    trailing := if qualified then [] else [.name "Token"],
    kind := .async, registration := .external, request := .nat, answer := .nat, cite := "finite review fixture" }
def externalProgram (param : String) : NativeEff :=
  .defs [{ name := "readExternal", request := .nat, answer := .nat, params := [q param] }]
    (.cons (.perform (.external 0) (.var 0)) .nil) (.succeed (.lit (.nat 1))) .nil

def service (methodParam initParam : Bool) : NativeEff :=
  .defs [
    { name := "makeCounter", request := .unit, answer := .nat, role := .serviceInit "Counter",
      params := if initParam then [q "use"] else [] },
    { name := "readCounter", request := .nat, answer := .nat, role := .serviceMethod "Counter" "read" 0,
      params := if methodParam then [q "use"] else [] }]
    (.cons (if initParam then .perform (.param 0) (.lit (.nat 7)) else .succeed (.lit (.nat 7)))
      (.cons (if methodParam then .perform (.param 0) (.var 0) else .succeed (.var 0)) .nil))
    (.succeed (.lit (.nat 1))) .nil

def onlyParamTy : Ty := .record [("_tag", false, .lit "OnlyParam"), ("id", false, .nat)]
def onlyParam (ordinaryColumn : Bool) : NativeEff :=
  .defs [{ name := "onlyHelper", request := (if ordinaryColumn then onlyParamTy else .nat), answer := .nat, params := [{ name := "use", request := onlyParamTy, answer := .nat }] }]
    (.cons (.succeed (.lit (.nat 1))) .nil) (.succeed (.lit (.nat 1))) .nil

def cases : List (String × NativeEff × RowTable) :=
  [("plain-positive", plain, []),
   ("payload-negative", payload "Payload", []), ("payload-positive", payload "use", []),
   ("qualified-negative", externalProgram "Widget", [externalRow true]),
   ("qualified-positive", externalProgram "use", [externalRow true]),
   ("trailing-negative", externalProgram "Token", [externalRow false]),
   ("trailing-positive", externalProgram "use", [externalRow false]),
   ("service-positive", service false false, []),
   ("service-method-negative", service true false, []),
   ("service-init-negative", service false true, []),
   ("parameter-class-negative", onlyParam false, []),
   ("parameter-class-positive", onlyParam true, [])]

#guard cases.all (fun (_, program, table) => Api.wellTyped program table)
#guard cases.all (fun (_, program, table) => (Api.printModule "main" program table).isSome)
#guard (Api.printModule "main" plain).map (fun m => decide (Api.readModule m [] = .ok plain)) == some true

#eval do
  for (name, program, table) in cases do
    let some m := Api.printModule "main" program table | throw (IO.userError name)
    IO.println <| Lean.Json.compress <| Lean.Json.mkObj
      [("name", Lean.toJson name),
       ("typeChecked", Lean.toJson (Api.wellTyped program table)),
       ("readsBack", Lean.toJson (decide (Api.readModule m table = Except.ok program))),
       ("source", Lean.toJson (TypeScript.Render.module TypeScript.house0 m))]
end HO3GeneratedFollowup
