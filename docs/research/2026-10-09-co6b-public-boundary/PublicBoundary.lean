import Effect4.Api
import TypeScript.Render

/-! Finite controls for checked module reading and service export generation.
Placement: exact-codecs, module-defs-round-trip, R5/R8, decisions 338/339.
Observation: an exported service method result, separately from the root result.
No new theorem, host simulation, or resource-lifetime claim is stated here. -/

namespace Co6bPublic
open Effect4.Program Effect4.Codegen

/-- Independent small service: initialize a number, then return the captured number. -/
def service : NativeEff :=
  .defs
    [{ name := "mkS", request := .unit, answer := .nat, role := .serviceInit "S" },
     { name := "readS", request := .nat, answer := .nat,
       role := .serviceMethod "S" "get" 0 }]
    (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.var 0)) .nil))
    (.perform (.call 0) (.lit .unit))

def twoServices (other : String) : NativeEff :=
  .defs
    [{ name := "mkS", request := .unit, answer := .nat, role := .serviceInit "S" },
     { name := "readS", request := .nat, answer := .nat, role := .serviceMethod "S" "get" 0 },
     { name := "mkT", request := .unit, answer := .nat, role := .serviceInit other },
     { name := "readT", request := .nat, answer := .nat, role := .serviceMethod other "get" 0 }]
    (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.var 0))
      (.cons (.succeed (.lit (.nat 2))) (.cons (.succeed (.var 0)) .nil))))
    (.succeed (.lit (.nat 0)))

def ambient : List TypeScript.Import := [.named ["Effect", "Context", "Layer"] "effect"]

def moduleOf (program : NativeEff) : TypeScript.Module :=
  match Effect4.Api.emitModule "main" program with
  | .ok emitted => emitted.module
  | .error _ => { header := [], imports := [], decls := [] }

/-- Change one source argument while retaining names, declarations, and types. -/
def changeRequest (c : TypeScript.ConstDecl) : TypeScript.ConstDecl :=
  if c.name ≠ "SLayer" then c else
  match c.value with
  | .call (.ident "Layer.effect") [.ident s, .call (.ident "Effect.map")
      [initial, .arrowBlock params [.ret (.object [(m, .lambda ps (.call (.ident d) [_]) none)])] none]] =>
    { c with value := .call (.ident "Layer.effect") [.ident s, .call (.ident "Effect.map")
      [initial, .arrowBlock params [.ret (.object [(m, .lambda ps (.call (.ident d) [.int 99]))])]]] }
  | _ => c

def changed (module : TypeScript.Module) : TypeScript.Module :=
  { module with decls := module.decls.map fun
      | .const c => .const (changeRequest c)
      | d => d }

def reading (module : TypeScript.Module) :=
  Effect4.Api.admitModule "main" module [] effectOrigins ambient

def refusalName : SurfaceRefusal → String
  | .unbound => "unbound"
  | .read _ => "read"
  | .illTyped => "illTyped"
  | .unrepresentable _ => "unrepresentable"
  | .unsafeName n => "unsafeName:" ++ n
  | .exportName _ n => "exportName:" ++ n
  | .notExported n => "notExported:" ++ n
  | .declaredType _ _ => "declaredType"
  | .layerDeclaration n => "layerDeclaration:" ++ n
  | .formation _ => "formation"
  | .classDeclarations => "classDeclarations"

def status (module : TypeScript.Module) : String :=
  match reading module with
  | .ok _ => "accepted"
  | .error why => refusalName why

#guard (Effect4.Api.emitModule "main" service).isOk
#guard Effect4.Api.readModule (moduleOf service) == .ok service
#guard match reading (moduleOf service) with
  | .ok result => result.program == service
  | .error _ => false

-- A binding control verifies that this setup uses the checked boundary.
#guard match Effect4.Api.admitModule "main" (moduleOf service) [] effectOrigins
    [.named ["Effect"] "effect"] with
  | .error .unbound => true
  | _ => false

#guard changed (moduleOf service) != moduleOf service
#guard Effect4.Api.readModule (changed (moduleOf service)) == .ok service
#guard match reading (changed (moduleOf service)) with
  | .ok result => result.program == service &&
      (moduleOf result.program == moduleOf service) &&
      (moduleOf result.program != changed (moduleOf service))
  | .error _ => false

#guard (Effect4.Api.emitModule "main" (twoServices "T")).isOk
#guard (reading (moduleOf (twoServices "T"))).isOk
#guard (Effect4.Api.emitModule "main" (twoServices "SLayer")).isOk
#guard match reading (moduleOf (twoServices "SLayer")) with
  | .error .unbound => true
  | _ => false

end Co6bPublic
open Co6bPublic

def main : IO Unit := do
  IO.println ("canonical-service: " ++ status (moduleOf service))
  IO.println ("changed-argument: " ++ status (changed (moduleOf service)))
  IO.println ("distinct-service-names: " ++ status (moduleOf (twoServices "T")))
  IO.println ("colliding-service-names: " ++ status (moduleOf (twoServices "SLayer")))
  for (name, module) in [("canonical.ts", moduleOf service),
      ("changed.ts", changed (moduleOf service)),
      ("distinct.ts", moduleOf (twoServices "T")),
      ("collision.ts", moduleOf (twoServices "SLayer"))] do
    IO.FS.writeFile ("docs/research/2026-10-09-co6b-public-boundary/" ++ name)
      (TypeScript.Render.module TypeScript.house0 { module with imports := ambient })
  IO.println "PASS: actual public emit/read/admit controls"
