import Effect4.Codegen.Checked
import Effect4.Codegen.Read
import Effect4.Codegen.SourceBindings

/-!
# Checked reading of a declaration block

`Program.readModule` is the raw reconstruction: it takes the last `const` as the main
program and ignores its name, its export flag, its annotation and the module's imports.
This module is the checked boundary beside it, in the way `emitModule` sits beside
`printModule`: `admitModule` runs the lexical binding check on the original module, the
raw reconstruction, the one whole-program checker, and a comparison of the declaration
envelope with what the printer would have emitted for the checked type, and keeps all four
as a certificate indexed by the exact module it read.

What it does **not** do. There is no widening of a declared type: the comparison is
equality with `Program.declarationType` of the certificate's own type, since the core has
no subsumption at a program's top type. Binder and local annotations are still refused by
the raw reader, not admitted. A resolved `Effect` name is a lexical fact, not evidence that
the host's `effect` package means what this tree means by it. Nothing here is target type
checking or execution.
-/

namespace Effect4.Codegen

open Effect4.Program

/-- The closed refusal alphabet of the reading boundary; the existing alphabets nest
rather than being re-listed. `DecidableEq` only: the carrier's `TypeRef` has decidable
equality but no `Repr`, and `declaredType` carries two of them. -/
inductive SurfaceRefusal where
  /-- The lexical check refused: an import, or a reference with no binding in its scope. -/
  | unbound
  | read (why : ReadRefusal)
  /-- The reconstructed program does not type against the signature. -/
  | illTyped
  /-- The checked type has no target annotation, so no declaration could be compared. -/
  | unrepresentable (why : PrintRefusal)
  | unsafeName (name : String)
  | exportName (expected actual : String)
  | notExported (name : String)
  | declaredType (expected actual : Option TypeScript.TypeRef)
  | layerDeclaration (name : String)
  deriving DecidableEq

/-- Every earlier declaration of a block is a plain exported layer constant: the shape
`printModule` gives them, and the shape the raw reader's `L_<path>` decoding assumes. -/
def layersPlain : List TypeScript.Decl → Option SurfaceRefusal
  | [] => none
  | .const c :: rest =>
    if c.type = none ∧ c.exported = true then layersPlain rest
    else some (.layerDeclaration c.name)
  | _ :: _ => some (.read (.shape "module"))

/-- The block's last declaration, when it is the exported constant shape the reader takes
as the main program. -/
def mainConst (decls : List TypeScript.Decl) : Option TypeScript.ConstDecl :=
  match decls.getLast? with
  | some (.const main) => some main
  | _ => none

/-- The envelope of a declaration block around a checked type: the export name is safe, the
last declaration is the exported main constant under that name annotated exactly as the
printer annotates the type, and every earlier declaration is a plain layer constant. `none`
means the envelope agrees; otherwise the first disagreement, named. -/
def envelopeCheck (name : String) (ty : EffTy) (decls : List TypeScript.Decl) :
    Option SurfaceRefusal :=
  if exportNameSafe name ≠ true then some (.unsafeName name)
  else
    match declarationType ty with
    | .error why => some (.unrepresentable why)
    | .ok expected =>
      match mainConst decls with
      | none => some (.read (.shape "module"))
      | some main =>
        if main.name ≠ name then some (.exportName name main.name)
        else if main.exported ≠ true then some (.notExported name)
        else if main.type ≠ expected then some (.declaredType expected main.type)
        else layersPlain decls.dropLast

/-- The `effect` namespaces the printer's heads and the native rows use, as permitted
import origins by name or as the whole package. `Exit`, `Option` and `Result` are here for
printed values; the rest are the head table's own namespaces. -/
def effectNamespaces : List String :=
  ["Effect", "Layer", "Ref", "Fiber", "Cause", "Deferred", "Scope", "Context",
    "Exit", "Option", "Result"]

/-- The permitted origins a standalone Effect module is read against. -/
def effectOrigins : List Bindings.Origin :=
  effectNamespaces.map (fun ns => .imported "effect" (some ns)) ++ [.imported "effect" none]

/-- A module with a host's ambient bindings prepended. An embedding host passes the prelude
it wraps the block in; a standalone module passes nothing. The check is never skipped. -/
def withAmbient (ambient : List TypeScript.Import) (module : TypeScript.Module) :
    TypeScript.Module :=
  { module with imports := ambient ++ module.imports }

/-- What the reading boundary checked, for exactly this module, table and export name.
`program` and `typing` are functions of `module`, so two readings of one module are equal. -/
structure ModuleReading (table : RowTable) (name : String) (allowed : List Bindings.Origin)
    (ambient : List TypeScript.Import) where
  module : TypeScript.Module
  program : NativeEff
  typing : TypedProgram (nativeSignature table) program
  bound : SourceBindings.Checked allowed (withAmbient ambient module)
  read : Program.readModule (nativeSignature table) (nativeSpell table) module.decls = .ok program
  envelope : envelopeCheck name typing.ty module.decls = none

/-- Checked reading: lexical bindings, raw reconstruction, the shared typing certificate,
and the declaration envelope compared with what the printer emits for the checked type. -/
def admitModule (name : String) (module : TypeScript.Module) (table : RowTable := [])
    (allowed : List Bindings.Origin := effectOrigins)
    (ambient : List TypeScript.Import := []) :
    Except SurfaceRefusal (ModuleReading table name allowed ambient) :=
  match SourceBindings.validate allowed (withAmbient ambient module) with
  | none => .error .unbound
  | some bound =>
    match hread : Program.readModule (nativeSignature table) (nativeSpell table) module.decls with
    | .error why => .error (.read why)
    | .ok program =>
      match checkTypedProgram (nativeSignature table) program with
      | none => .error .illTyped
      | some typing =>
        match henv : envelopeCheck name typing.ty module.decls with
        | some why => .error why
        | none => .ok ⟨module, program, typing, bound, hread, henv⟩

end Effect4.Codegen
