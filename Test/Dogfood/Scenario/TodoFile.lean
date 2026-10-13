import Test.Dogfood.Scenario.Todo
import Effect4.Program.Authoring.ApplicationService
import Effect4.Laws.Api.ModuleReadable

/-!
# The to-do's emitted file reads back whole (decisions row 378 (19), (20); seat READ)

The application's file holds its payload classes, then its rows' services, then the declaration
block (`ModuleEmission.file`, `src/Effect4/Codegen/Checked.lean`). The file reader reads the
services back exactly (`readRowServices`, `src/Effect4/Codegen/RowServices.lean`) and the block
under the module's classes (`readDefHead`, `src/Effect4/Codegen/Read.lean`), so the file reads back
to the built program (`Api.readFile`). The envelope that a host wraps holds no service, and reads
back by `Api.readModule`. The laws are `ModuleEmission.readFile` and `ModuleEmission.readModule`
(`src/Effect4/Laws/Api/ModuleReadable.lean`). Neither states that tsgo accepts the file or that
rc.112 runs it: seat SVC's E4 lane holds that evidence.

Each line is a finite evaluation or a control (decisions row 301).
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.TodoFile

open Effect4 Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.Scenario.Todo

/-- The service's name. -/
def service : String := "TodoApp"

/-- An application's module with its service, built. -/
def built? (app : Application NativeOp) : Option Api.Built :=
  (app.serviceModule service).toOption.bind fun m => (Effect4.Api.Author.build m).toOption

/-- The built program, its table, its envelope and its file (the prelude at `./prelude.ts`). -/
def emitted? (app : Application NativeOp) :
    Option (Api.Program × RowTable × TypeScript.Module × TypeScript.Module) :=
  (built? app).bind fun b => (Effect4.Api.emitModule "main" b.program b.table).toOption.bind fun e =>
    (e.file "./prelude.ts").toOption.map fun f => (b.program, b.table, e.module, f)

/-- A module whose declarations are replaced. -/
def withDecls (m : TypeScript.Module) (decls : List TypeScript.Decl) : TypeScript.Module :=
  { m with decls := decls }

/-- The file's declarations with the one at position `i` replaced by `f` of it. -/
def editConst (m : TypeScript.Module) (i : Nat) (f : TypeScript.ConstDecl → TypeScript.ConstDecl) :
    TypeScript.Module :=
  withDecls m (m.decls.modify i fun
    | .const c => .const (f c)
    | d => d)

/-! ## The file and the envelope read back -/

-- reader: the to-do's file reads back to its built program
#guard (emitted? application).map (fun (p, table, _, file) =>
  decide (Api.readFile file table = .ok p)) = some true
-- reader: the envelope, which holds no service, reads back by the envelope reader
#guard (emitted? application).map (fun (p, table, envelope, _) =>
  decide (Api.readModule envelope table = .ok p)) = some true
-- control: each reader refuses the other's form; the file's services are no layer, and the
-- envelope lacks the services that the file reader asks of the table
#guard (emitted? application).map (fun (_, table, envelope, file) =>
  (Api.readModule file table matches .error _) &&
    (Api.readFile envelope table matches .error (.shape "row services"))) = some true

/-! ## The services, exactly

The file's first two constants after the class are the repository's key and its namespace. -/

-- finite evaluation: the file's constants begin with the rows' service, key first
#guard (emitted? application).map (fun (_, _, _, file) => (file.decls.drop 1).take 2 |>.map fun
  | .const c => c.name
  | _ => "") = some ["TodoRepoKey", "TodoRepo"]
-- control: a key at another identity is refused
#guard (emitted? application).map (fun (_, table, _, file) =>
  Api.readFile (editConst file 1 fun c => { c with value := match c.value with
    | .call (.generic h [_, shape]) [_] =>
      .call (.generic h [.literal "k30_7", shape]) [.str "k30_7"]
    | v => v }) table matches .error (.shape "row services")) = some true
-- control: the namespace's accessor calling another method is refused
#guard (emitted? application).map (fun (_, table, _, file) =>
  Api.readFile (editConst file 2 fun c => { c with value := match c.value with
    | .call h [k, .object ((m, _) :: rest)] =>
      .call h [k, .object ((m, accessorExpr "TodoRepoKey" "all" none) :: rest)]
    | v => v }) table matches .error (.shape "row services")) = some true
-- control: the two declarations in the other order are refused
#guard (emitted? application).map (fun (_, table, _, file) =>
  match file.decls with
  | c :: k :: n :: rest =>
    (Api.readFile (withDecls file (c :: n :: k :: rest)) table matches .error (.shape "row services"))
  | _ => false) = some true

end Test.Dogfood.Scenario.TodoFile
