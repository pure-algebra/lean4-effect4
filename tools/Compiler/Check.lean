import Compiler.Json
import Effect4.Program.Authoring.ApplicationService
import Effect4.Api.Author
import Effect4.Api.RefusalsDerived
import Compiler.Code.Module

/-!
# Compiler.Check — an application checked, and its certificate

The compile's first two folds (`docs/research/2026-10-20-compiler-entry/README.md`, §2 and §5):
the application's service module (`Application.serviceModule`), elaborated and built
(`Api.Author.build`). The build is formation, the table, typing and admission at the
application, so the built program carries its certificate (`Api.Built.admitted`).

- **The service** is named for the application (`serviceName`): its name with a capital first
  letter, then `App`. The printed module exports the service under that name.
- **A refusal** is the build's located refusal (`CheckRefusal`). When the service block refuses an
  entry's open program, the refusal is the same case of the build's alphabet, located in that
  entry's open program, and the entry is named beside it. It prints through the generated encoder
  of `Api.BuildRefusal` (`src/Effect4/Api/RefusalsDerived.lean`), as JSON or as that JSON's text:
  no second spelling.
- **The certificate** (`certificate`) is the built program's answer, error and required keys, its
  rows, the names its rows give their service keys (`Signature.keyNames`), and its definitions'
  declarations, each in its carrier's one public JSON (`Compiler.Json`, decisions row 418).
  `certificateLines` is the same certificate as text.

What it does not establish: profile support, which a target's emission checks (`Compiler.Emit`),
and any run.
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Store
open Effect4.Machine.Env (Requirement)

/-- **An application's service**: its name with a capital first letter, then `App` (`todo` gives
`TodoApp`). -/
def serviceName (app : Application NativeOp) : String := app.name.capitalize ++ "App"

/-- **Why `check` refuses**: the build's located refusal, and the entry whose open program it is
located in when the service block refuses that entry before the build. -/
structure CheckRefusal where
  entry : Option String
  why : Api.BuildRefusal

/-- A refusal as JSON: the entry, when there is one, and the refusal's generated print. -/
def CheckRefusal.json (r : CheckRefusal) : NatJson :=
  .obj ((r.entry.map fun e => [("entry", .str e)]).getD [] ++ [("refused", tree r.why)])

/-- A refusal as text: where it is, then its generated print's text. -/
def CheckRefusal.text (r : CheckRefusal) : String :=
  (r.entry.map fun e => s!"the entry {e} is refused: ").getD "refused: " ++ jsonText (tree r.why)

/-- **The application checked**: its service module, elaborated and built; or the refusal, located. -/
def check (app : Application NativeOp) : Except CheckRefusal Api.Built :=
  match app.serviceModule (serviceName app) with
  | .error (.scope e r) => .error ⟨some e, .scope r⟩
  | .error (.typing e r) => .error ⟨some e, .typing r⟩
  | .ok m => (Api.Author.build m).mapError (⟨none, ·⟩)

/-- **A program checked at the empty application** (`Api.Built.ofProgram`): built, or the build's
refusal at admission. A program of the wire corpus is one, and so is each program of a group. -/
def checkProgram (program : NativeEff) : Except CheckRefusal Api.Built :=
  (Api.Built.ofProgram {} program).mapError fun why => ⟨none, .admission why⟩

/-- **The certificate of a built program**, as `check --json` prints it and `certificate.json`
holds it: the answer, the error and the keys required, the rows, the services' keys with their
names, and the definitions' declarations. -/
def certificate (b : Api.Built) : NatJson :=
  .obj [("answer", tree b.ty.answer), ("error", tree b.ty.error), ("requires", tree b.requires),
    ("rows", tree b.table), ("services", tree (nativeSignature b.table).keyNames),
    ("declarations", tree b.program.defsOf)]

/-- A column's text: the request, then its type (`Tools.Code.effTyText`). -/
def columnText (request answer error : Ty) (requires : List ServiceKey) : String :=
  s!"({request.render}) " ++ Tools.Code.effTyText ⟨answer, error, Requirement.ofList requires⟩

/-- A header row's lines, or `none` for an empty list. -/
def orNone (lines : List String) : List String := if lines.isEmpty then ["none"] else lines

/-- **The certificate as text**, as `check` prints it, laid out as a header block
(`Tools.Code.headerBlock`): the program's address, its type, its rows, its services' names and
keys, and its definitions. -/
def certificateLines (title : String) (b : Api.Built) : List String :=
  Tools.Code.headerBlock title
    [("program", [s!"sha256 {Tools.Code.addressOf b.program}"]),
     ("type", [Tools.Code.effTyText b.ty]),
     ("rows", orNone (b.table.map fun r => r.spelling ++ columnText r.request r.answer r.error r.requires)),
     ("services", orNone ((nativeSignature b.table).keyNames.map fun (k, n) => s!"{n} {keyText k}")),
     ("defines", orNone (b.program.defsOf.map fun d =>
        d.name ++ columnText d.request d.answer d.error d.requires))]

end Compiler
