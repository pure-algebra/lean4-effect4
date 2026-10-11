import Effect4.Api
import TypeScript.Render
import Test.Codegen.ServicesPrint

/-! Finite controls for checked module reading and service export generation.
Placement: exact-codecs, module-defs-round-trip, R5/R8, decisions 338/339.
Observation: an exported service method result, separately from the root result.
No new theorem, host simulation, or resource-lifetime claim is stated here. -/

namespace Co6bPublic
open Effect4.Program Effect4.Codegen

/-- Independent small service: initialize a number, then return the captured number. -/
def service (methodName : String := "get") : NativeEff :=
  .defs
    [{ name := "mkS", request := .unit, answer := .nat, role := .serviceInit "S" },
     { name := "readS", request := .nat, answer := .nat,
       role := .serviceMethod "S" methodName 0 }]
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
#guard (reading (moduleOf service)).isOk
#guard changed (moduleOf service) != moduleOf service
#guard (Effect4.Api.readModule (changed (moduleOf service))).toOption.isNone
#guard (reading (changed (moduleOf service))).toOption.isNone
#guard (Effect4.Api.emitModule "main" (twoServices "T")).isOk
#guard (reading (moduleOf (twoServices "T"))).isOk
#guard (Effect4.Api.emitModule "main" (twoServices "SLayer")).toOption.isNone
#guard (Effect4.Api.emitModule "main" (service "bad-name")).toOption.isNone
#guard (Effect4.Api.emitModule "main" (service "__proto__")).toOption.isNone

/-- Add a second exported method with its own name and the same definition. -/
def addAlias (c : TypeScript.ConstDecl) : TypeScript.ConstDecl :=
  if c.name = "S" then
    match c.value with
    | .call (.generic h [t, .object [f]]) args =>
      { c with value := .call (.generic h [t, .object [f, { f with name := "alias" }]]) args }
    | _ => c
  else if c.name = "SLayer" then
    match c.value with
    | .call h [key, .call f [initial, .arrowBlock params [.ret (.object [(name, body)])] ret]] =>
      { c with value := .call h [key, .call f [initial,
        .arrowBlock params [.ret (.object [(name, body), ("alias", body)])] ret]] }
    | _ => c
  else c

def aliasModule : TypeScript.Module :=
  let m := moduleOf service
  { m with decls := m.decls.map fun | .const c => .const (addAlias c) | d => d }

-- The additional method reaches the checked boundary and disappears in reconstruction.
#guard aliasModule != moduleOf service
#guard Effect4.Api.readModule aliasModule == .ok service
#guard match reading aliasModule with
  | .ok result => result.program == service && moduleOf result.program != aliasModule
  | .error _ => false

/-- A local control of metadata coverage, using the existing service-information projection.
This is a proposed reader check, not an implementation change. -/
def rolesCoverServiceInfo (m : TypeScript.Module) : Bool :=
  let cs := m.decls.filterMap fun | .const c => if isServiceConst c then some c else none | _ => none
  match readServices cs, Effect4.Api.readModule m with
  | some infos, .ok (.defs defs _ _) => infos == (servicesOf defs).map (serviceInfo defs)
  | _, _ => false

#guard rolesCoverServiceInfo (moduleOf service)
#guard rolesCoverServiceInfo (moduleOf (twoServices "T"))
#guard !rolesCoverServiceInfo aliasModule

-- The request reader rejects a swap in a method with two explicit arguments.
#guard isMethodRequest ["a1", "a2"]
  (.call (.ident "pair") [.ident "a0", .call (.ident "pair") [.ident "a1", .ident "a2"]])
#guard !isMethodRequest ["a1", "a2"]
  (.call (.ident "pair") [.ident "a0", .call (.ident "pair") [.ident "a2", .ident "a1"]])

end Co6bPublic

namespace SemaphoreCoverage
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- A client that distinguishes one captured semaphore from fresh state for each method. -/
def strongerModule : Module NativeOp :=
  { defs := Semaphore.serviceDefs "Permits" 2,
    main := eff do
      let s ← Def.invoke "semaphoreMake" []
      let a ← Def.invoke "semaphoreTake" [s, nat 2]
      let b ← Def.invoke "semaphoreTakeIfAvailable" [s, nat 1]
      let c ← Def.invoke "semaphoreRelease" [s, nat 1]
      return tuple [a, b, c] }

def strongerProgram : Option Api.Program :=
  (Api.Author.build strongerModule).toOption.map (·.program)

#guard strongerProgram.isSome
#guard strongerProgram.map (fun p => (Api.run p 1000).exit) =
  some (some (.success (.list [.nat 2, .bool false, .nat 1])))
#guard strongerProgram.map (fun p => (Api.runSync p 1000).2) =
  some (.success (.list [.nat 2, .bool false, .nat 1]))

end SemaphoreCoverage

open Co6bPublic

def main : IO Unit := do
  let dir := "docs/research/2026-10-10-service-repair-overwatch/"
  for (name, m) in [("canonical.ts", moduleOf service), ("alias.ts", aliasModule)] do
    IO.FS.writeFile (dir ++ name)
      (TypeScript.Render.module TypeScript.house0 { m with imports := ambient })
  match SemaphoreCoverage.strongerProgram.bind (Effect4.Api.printModule "main") with
  | none => throw (IO.userError "stronger Semaphore module did not print")
  | some m => IO.FS.writeFile (dir ++ "semaphore-stronger-decl.ts") (TypeScript.Render.module TypeScript.house0 m)
  IO.println "PASS: retained service repairs; checked reader drops alias; stronger Semaphore answers [2,false,1]"
