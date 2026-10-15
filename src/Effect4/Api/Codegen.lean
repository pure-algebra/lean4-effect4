import Effect4.Api.Built
import Effect4.Codegen.Print
import Effect4.Codegen.Checked
import Effect4.Codegen.SourceBindings
import Effect4.Codegen.Read
import Effect4.Codegen.Admit
import Effect4.Codegen.CallbackRequirements
import Effect4.Codegen.Schema
import Effect4.Codegen.Target

/-!
# Effect4.Api.Codegen — the program interface's codegen face

The half of the application face that crosses to TypeScript, in the namespace `Effect4.Api`:

* `print` / `printDecl` answer TypeScript **syntax** (`TypeScript.Expr`, `ConstDecl`), never
  text. Rendering to bytes is one call to the pinned package — `TypeScript.Render.expr house0 0
  e` — kept outside this module on purpose: Lean's `String` folds reach `Classical.choice`, and
  this module stays at the library's axiom ceiling.
* `read`, `readAt`, `readable` and `roundTrip` are the reader and the print image's round trip;
  `imageCertificate` carries `readable` as a certificate.
* `emitModule`, `printModule`, `readModule`, `readFile`, `checkSourceBindings` and `admitModule`
  are the module's production receipt, its raw reconstruction and its checked reading.
* `Typed.print`, `Typed.emit`, `TypedLayer.print` and `Built.print` print the certified values.
* The Schema half: persisted `SchemaRepresentation` JSON syntax (`schemaDocument`,
  `schemaRepresentation`) and the JSON payload beside it (`jsonExpr`).
  `Codegen.Schema.moduleSyntax` assembles raw module syntax; `Effect4.Codegen.Schema.documentSource`
  renders one raw document and is admitted by exact name in the axiom gate. A document's
  references table is written once per key, and a repeated key whose bodies differ is refused
  (decisions row 8 (C)).
* The codegen crossing: `Target` and `Artefact` represent emitted syntax, and `render` is the one
  crossing from an artefact to bytes — admitted by exact name in the gate as
  `Effect4.Codegen.Artefact.render`, and the reason the rest of this face never returns text.

The face is its own module so that the program interface below it (`Effect4.Api`, its authoring
and session faces, and the law graph that reads them) imports no codegen module: an edit of the
printer, the reader or the module writer rebuilds this module's importers, not the interface's.
The root `Effect4` imports it, so an application that imports the root sees one face. The
refusal alphabets it answers in are the interface's own (`Codegen/Refusal.lean`).
-/

namespace Effect4.Api

open Effect4 Effect4.Machine Effect4.Program

/-! ## Printing and reading -/

/-- The program as one TypeScript expression, at the empty environment. -/
def print (program : Program) (table : RowTable := []) : Except PrintRefusal TypeScript.Expr :=
  Program.print (nativeSignature table) 0 program

/-- A program back from one TypeScript expression, at the empty environment: read through the
table the printer prints from (`src/Effect4/Codegen/Read.lean`, `readT`), a `ReadRefusal` on a
tree no row matches. A row is accepted only when the printer would choose it for what was
read, so what is read prints back to the tree read (`read_exact`). A payload class construction
`new Tag({ … })` reads under the module's `classes` (decisions row 120); a bare expression has
none. -/
def read (expression : TypeScript.Expr) (table : RowTable := [])
    (classes : Effect4.Codegen.Classes.Classes := []) : Except ReadRefusal Program :=
  Program.readEff classes (nativeSignature table) (nativeSpell table) 0 expression

/-- `read`, with where a refusal happened: the path of constructors and argument indices down to
the node that refused, and, when a reserved head matched no row, what the nearest row's skeleton
has where the tree parts from it (`Effect4.Program.ReadFailure`; `.render` for a person). -/
def readAt (expression : TypeScript.Expr) (table : RowTable := [])
    (classes : Effect4.Codegen.Classes.Classes := []) : Except Program.ReadFailure Program :=
  Program.readEffAt classes (nativeSignature table) (nativeSpell table) 0 expression

/-- Whether `read` of the program's printing is the program itself: the round trip, decided by
running it. What the printer loses is listed in `Codegen/Read.lean`'s module note (a variable
out of scope, a dropped `unit` request, a stated type outside the readable types, the internal
fiber actions).
A program the printer refuses is not readable either: a child fork into a scope has no rc.112
spelling, so it is refused (`internalAction "forkScoped:child"`, `Codegen/Templates.lean`), never
printed as the daemon it is not. -/
def readable (program : Program) (table : RowTable := []) : Bool :=
  Program.readable (nativeSignature table) (nativeSpell table) 0 program

/-- `read` after `print`: the program itself exactly when it is `readable`
(`Effect4.Program.roundTrip_eq`), and otherwise the program the printer kept. -/
def roundTrip (program : Program) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.roundTrip (nativeSignature table) (nativeSpell table) 0 program

/-- The print-image certificate, separate from admission on purpose: the proof that this
program survives `print` and `read` unchanged. A program without it still runs.

`PLift` only because `Option` is a `Type` and the certificate is a `Prop`; the proposition
carried is exactly `readable program table = true`, reached as `.down`. -/
def imageCertificate (program : Program) (table : RowTable := []) :
    Option (PLift (readable program table = true)) :=
  if h : readable program table = true then some ⟨h⟩ else none

/-! ## Modules: production, reconstruction, checked reading -/

/-- The program as an exported constant with its `Effect.Effect<A, E>` type, its body printed as
a module that ships prints it (`Program.shippedPieces`: the typed print, a call's type arguments
where a join needs them, or the fold where the typed print refuses). Raw formation,
stored-annotation support, typing and printing must all succeed; otherwise the result is
`none`. -/
def printDecl (name : String) (program : Program) (table : RowTable := []) : Option TypeScript.ConstDecl :=
  match Program.Formation.checkInput program table, Program.annotationRefusal program with
  | none, none =>
    match checkTyping program table, Program.shippedPieces (nativeSignature table) [] program with
    | some typing, Except.ok body => (Program.printDecl name typing.ty body).toOption
    | _, _ => none
  | _, _ => none


/-- The module together with its core typing and exact production receipt. Consumers
that need the proof connection retain this result; `printModule` projects its syntax.
This does not validate source imports or establish target typing/execution. -/
def emitModule (name : String) (program : Program) (table : RowTable := []) :
    Except Effect4.Codegen.EmissionRefusal (Effect4.Codegen.ModuleEmission program table name) :=
  -- a callback that needs a service is refused at its invocation until the header can carry its
  -- row (`Codegen/CallbackRequirements.lean`, Codex's HO3-REQ-01)
  match Effect4.Codegen.invokeRequirementFault (nativeSignature table) program with
  | some path => .error (.print (.callbackRequirement path))
  | none => Effect4.Codegen.emitModule name program table

/-- The program as a declaration block: one `const L_<path> = …` per referenced layer target
(the host rows slice, `Program.printModule`), then the exported main constant; `none` when it
is ill-typed or the printer refuses it. `Api.emitModule` answers the refusal's reason; an
export name with an `exportNameFault` is one. The block is what a host must run for a program
with a layer reference: rc.112 keys its memo map on the layer object (`Layer.ts:411`), and the
one `const` is the one object. -/
def printModule (name : String) (program : Program) (table : RowTable := []) : Option TypeScript.Module :=
  ((emitModule name program table).toOption).map (·.module)

/-- Reconstruction from a declaration block, each program piece read after the named erasure of
the type arguments that the typed print inserts (`Program.readModuleTyped`), so it reads the
block that `printModule` answers. This recovers programs in the printer's readable image, but
ignores imports, outer annotations and export names. Use `checkTyping` on the recovered program
for core typing; that check alone does not validate the original source envelope. -/
def readModule (module : TypeScript.Module) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.readModuleTyped (nativeSignature table) (nativeSpell table) NativeOp.call NativeOp.param []
    module.decls

/-- Reconstruction from a module file (`ModuleEmission.file`): the payload classes, then the
row namespaces' services (`rowServiceDecls`, decisions row 378 (19)), read back exactly against
the table, then the declaration block, read as `readModule` reads it. A module that declares no
service of its table reads by `readModule`; a file of a table with no service row reads by
either. -/
def readFile (module : TypeScript.Module) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.readModuleTyped (nativeSignature table) (nativeSpell table) NativeOp.call NativeOp.param
    table module.decls

/-- Check imports and lexical bindings on the original module, retaining its exact
syntax in the certificate's index. The caller supplies permitted import origins.
This is a prerequisite of typed source admission: it does not check annotation
agreement, resolve package exports or validate the origin expected by a core head. -/
def checkSourceBindings (module : TypeScript.Module)
    (allowed : List Effect4.Codegen.Bindings.Origin) :
    Option (Effect4.Codegen.SourceBindings.Checked allowed module) :=
  Effect4.Codegen.SourceBindings.validate allowed module

/-- Checked reading of a declaration block, the boundary `readModule` is the raw half of.
It checks four things and keeps all four: the original module's imports and lexical bindings
against the permitted origins (with a host's `ambient` prelude prepended), the raw
reconstruction of the program, the one whole-program type checker, and the declaration
envelope — a safe export name, the last declaration exported under that name and annotated
exactly as `printDecl` annotates the checked type, and every earlier declaration a plain
exported layer constant.

What it does **not** check. It does not widen a declared type: the comparison is equality
with the printer's own annotation, because the core has no subsumption at a program's top
type. It admits no binder, return or local annotation; the raw reader still refuses those.
It gives the `effect` package no meaning: a resolved `Effect` is a lexical fact, not
evidence that the host's namespace is the pinned one. It is neither target type checking
nor execution. -/
def admitModule (name : String) (module : TypeScript.Module) (table : RowTable := [])
    (allowed : List Effect4.Codegen.Bindings.Origin := Effect4.Codegen.effectOrigins)
    (ambient : List TypeScript.Import := []) :
    Except Effect4.Codegen.SurfaceRefusal
      (Effect4.Codegen.ModuleReading table name allowed ambient) :=
  Effect4.Codegen.admitModule name module table allowed ambient

/-! ## The certified values, printed -/

namespace Typed

variable {table : RowTable}

/-- The printed syntax of the certified program. -/
def print (t : Typed table) : Except PrintRefusal TypeScript.Expr := Api.print t.program table

/-- The certified module emission under a declaration name. -/
def emit (t : Typed table) (name : String) :
    Except Effect4.Codegen.EmissionRefusal (Effect4.Codegen.ModuleEmission t.program table name) :=
  Api.emitModule name t.program table

end Typed

namespace TypedLayer

variable {sig : Signature NativeOp}

/-- The printed layer (`Codegen.Templates.printLayerT`, the printer's own fold). -/
def print (l : TypedLayer sig) : Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printLayerT sig l.layer

end TypedLayer

namespace Built

/-- The printed syntax of the built program, against its own table. -/
def print (b : Built) : Except PrintRefusal TypeScript.Expr := b.typed.print

end Built

/-! ## Schema, as syntax -/

/-- A persisted Schema document as raw `SchemaRepresentation` JSON syntax, its references table
written once per key; a repeated key whose bodies differ is refused at `["references", key]`
(decisions row 8 (C)). -/
def schemaDocument (document : Effect4.Document) :
    Except Effect4.Codegen.Schema.ReferenceRefusal TypeScript.Expr :=
  Effect4.Codegen.Schema.documentExpr document

/-- A persisted representation as raw `SchemaRepresentation` JSON syntax. -/
def schemaRepresentation (representation : Effect4.Representation) : TypeScript.Expr :=
  Effect4.Codegen.Schema.representation representation

/-- A JSON payload as a TypeScript literal. -/
def jsonExpr (value : Effect4.Json) : TypeScript.Expr :=
  Effect4.Codegen.Schema.json value

/-! ## Codegen: the targets, artefacts, and rendering to bytes -/

export Effect4.Codegen (Target Artefact)
export Effect4.Codegen.Artefact (render)

end Effect4.Api
