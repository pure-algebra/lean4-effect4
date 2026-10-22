import Test.Api.SessionFixtures
import Effect4.Emit

/-! # Probe 5: the authoring surface, each form as the Lean an author writes, the `Eff` it
builds and the Effect TypeScript it prints to

Every form below is a combinator the tree has (`src/Effect4/Program/Authoring/`). Nothing is
added. The printed text is `TypeScript.Render.module` of `Api.emitModule`'s file, the gate's
own print.
Run: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-handlers/probe-api.lean`. -/

open Effect4 Effect4.Program Effect4.Api Effect4.Program.Authoring Test.Api.SessionFixtures
open Test.Dogfood.Scenario.Todo (application listCache todoRepoKey)

namespace Probe

/-- The printed file of a built program, as lines. -/
def printed (b : Built) : Option (List String) :=
  (Api.emitModule "main" b.program b.table).toOption.bind fun e =>
    (e.file "./prelude.ts").toOption.map fun f =>
      (TypeScript.Render.module TypeScript.house0 f).splitOn "\n"

/-- The lines that mention a name. -/
def linesWith (b : Built) (name : String) : Option (List String) :=
  (printed b).map fun ls => ls.filter fun l => (l.splitOn name).length > 1

/-- A program printed as one expression, at the native signature. -/
def exprOf (src : Src NativeOp) : Except String String := do
  let e ← (elaborate src).mapError (fun _ => "scope")
  let x ← (print (nativeSignature []) 0 e).mapError (fun _ => "print")
  pure (TypeScript.Render.expr TypeScript.house0 0 x)

/-- A service an author declares by key and carrier (`ServiceDef`). -/
def db : ServiceDef := { key := todoRepoKey, carrier := .unit }
def log : ServiceDef := { key := ⟨⟨31⟩, ⟨6⟩⟩, carrier := .unit }

/-- F3, vertical at the program: the body under one layer (`Authoring.provide`). -/
def vertical : Src NativeOp := provide (db.layer (succeed unit)) (ServiceDef.use db)

/-- F4, horizontal at the program: the body under two layers at one site (`provideAll`). -/
def horizontal : Src NativeOp :=
  provideAll [db.layer (succeed unit), log.layer (succeed unit)] (andThen (ServiceDef.use db) (ServiceDef.use log))

/-- F4', horizontal at the layer: `Layer.merge` is a constructor; its typing is the union of
the two signatures (`LayerTy.merge`). -/
def merged : LayerTerm NativeOp := .merge (.effect db.key (.succeed (.lit .unit))) (.effect log.key (.succeed (.lit .unit)))

def handlerNames (b : Built) : List String := (servicesOf b.program.defsOf).map (·.name)

end Probe

open Probe

-- F1. declare a handler: `application.serviceModule "TodoApp"` (the fixtures' `todoBuilt`)
#eval todoBuilt.map handlerNames
#eval todoBuilt.bind (linesWith · "TodoApp")
-- F2. impose a transformer: `{ application with imposed := [listCache] }` (`cachedBuilt`)
#eval cachedBuilt.map handlerNames
#eval cachedBuilt.bind (linesWith · "TodoAppLayer")
#eval cachedBuilt.bind (linesWith · "TodoApp_list")
-- F3. vertical: `provide layer body`
#eval exprOf vertical
-- F4. horizontal: `provideAll [l₁, l₂] body`
#eval exprOf horizontal
#eval (Checker.checkLayer (nativeSignature []) [] merged).toOption.map fun l => (l.out.elems.map keyText, l.requires.elems.map keyText)
-- F5. read the forwarded row: the layer's requirement is the init's; the methods' is discharged
#eval todoBuilt.bind (linesWith · "TodoAppContext")
