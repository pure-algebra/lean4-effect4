import Test.Dogfood.Scenario.Todo
import Effect4.Program.Authoring.ApplicationService
import Effect4.Laws.Api.ModuleReadable

/-!
# The to-do application as one Effect service (decisions row 378 (20), slices E1 and E2)

The application's entries become one service (`Application.serviceModule`,
`src/Effect4/Program/Authoring/ApplicationService.lean`). The module printer prints the service
as target syntax: an Effect service key and its layer. The file writes its imports from Lean data
(`ModuleEmission.file`, `src/Effect4/Codegen/Checked.lean`). The compiler's check of the file and
of a consumer program is in seat SVC's receipt (`docs/research/2026-10-13-seat-svc-receipt.md`).
It is the target's verdict, not this battery's.

Each line is a finite evaluation or a control (decisions row 301).
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.TodoService

open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Machine.Env (Requirement)
open Test.Dogfood.Scenario.Todo

/-- The service's name. -/
def service : String := "TodoApp"

/-- An application's module with its service, built. -/
def built? (app : Application NativeOp) : Option Api.Built :=
  (app.serviceModule service).toOption.bind fun m => (Effect4.Api.Author.build m).toOption

/-- The emitted file of an application's service, with the prelude at `./prelude.ts`. -/
def file? (app : Application NativeOp) : Option TypeScript.Module :=
  (built? app).bind fun b =>
    (Effect4.Api.emitModule "main" b.program b.table).toOption.bind fun e =>
      (e.file "./prelude.ts").toOption

/-- The constants of a module, in order. -/
def constNames (m : TypeScript.Module) : List String :=
  m.decls.filterMap fun d => match d with
    | .const c => some c.name
    | _ => none

/-- Whether an application's emitted module reads back to its built program. Beside it, whether
the program lies in the readable domain of a block (`blockReadable`). -/
def readBack? (app : Application NativeOp) : Option (Bool × Bool) :=
  (built? app).bind fun b => (Effect4.Api.emitModule "main" b.program b.table).toOption.map fun e =>
    (decide (Api.readModule e.module b.table = Except.ok b.program),
      blockReadable e.classes (nativeSignature b.table) b.program)

/-- The to-do without the two entries that fail with the payload class `NotFound`. -/
def classFree : Application NativeOp := { application with entries := application.entries.take 2 }

/-- The same, over rows that require no key: the state is the context of no key. -/
def keyFree : Application NativeOp :=
  { classFree with rows := classFree.rows.map fun r => ⟨{ r.row with requires := [] }⟩ }

/-! ## The block and the file -/

-- finite evaluation: the rows' service, its key first (decisions row 378 (19)); the initial
-- program and one method for each entry; then the service's key, its layer and the main
#guard (file? application).map constNames = some ["TodoRepoKey", "TodoRepo", "TodoAppContext",
  "TodoApp_add", "TodoApp_list", "TodoApp_complete", "TodoApp_remove", "TodoApp", "TodoAppLayer",
  "main"]
-- finite evaluation: the state is the context of the rows' one key
#guard application.contextKeys = Requirement.ofList [todoRepoKey]
#guard (built? application).map (fun b => b.program.defsOf.head?.map (·.answer)) =
  some (some (.contextOf (Requirement.ofList [todoRepoKey])))
-- finite evaluation: each method declares its entry's open type (`openTy`), and no requirement:
-- the region discharges the key
#guard (built? application).map (fun b => (b.program.defsOf.drop 1).map fun d =>
    (some (d.answer, d.error), d.requires)) =
  some (application.entryNames.map fun n => (openTy n, []))
-- finite evaluation: the file imports four namespaces of `effect`, `Option` as a type only (the
-- repository's `setDone` answers an option), and six prelude names; no name stays free, since the
-- file declares the rows' namespace and `Object` is a standard global
#guard (file? application).map (·.imports) =
  some [.named ["Context", "Data", "Effect", "Layer", ⟨"Option", "Option", true⟩] "effect" false,
    .named ["eq", "fst", "ifCase", "optionCase", "pair", "snd"] "./prelude.ts" false]
#guard (file? application).map Effect4.Codegen.freeNames = some []

/-! ## Reading back -/

-- finite evaluation: the to-do's module reads back. The header reader reads the payload class
-- `NotFound` in two methods' error columns and the rows' key in the requirement rows, so the
-- block is `blockReadable` and `ModuleEmission.readModule` reads it back (seat READ, item 1)
#guard readBack? application = some (true, true)
-- finite evaluation: without those two entries the block reads back too
#guard readBack? classFree = some (true, true)
-- finite evaluation: over rows that require no key the block is readable and reads back, so the
-- premises of the read-back law reach a class-free application whose rows require no key
#guard readBack? keyFree = some (true, true)

/-! ## A refused entry refuses the block, by its name -/

-- control: the scope reader refuses an unbound name
#guard match ({ application with entries := [{ name := "bad", body := succeed (var "nope") }] } :
    Application NativeOp).serviceDefs service with
  | .error (.scope "bad" ⟨_, .unbound "nope"⟩) => true
  | _ => false
-- control: the checker refuses a row called at another request
#guard match ({ application with
    entries := [{ name := "bad", params := [("n", .nat)], body := TodoRepo.insert (var "n") }] } :
    Application NativeOp).serviceDefs service with
  | .error (.typing "bad" _) => true
  | _ => false

end Test.Dogfood.Scenario.TodoService
