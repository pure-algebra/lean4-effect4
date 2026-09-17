import Effect4.Api
import Effect4.Laws.Codegen.Checked
import Effect4.Laws.Codegen.SourceBindings
import Effect4.Laws.Codegen.Admit

/-!
# The application module face on its readable, typed domain

Compose the shared-layer syntax laws through the actual API. Type checking supplies
reference validity, the codegen table supplies spelling hygiene, readability is
the exact-image premise, and the export name must be one the reader can tell from a
printed binder, a reserved head and a layer reference name. No successful output is
assumed. These are theorems about the module AST returned by the existing API.

`admitModule_emitModule` is the round trip in certificate form: what the checked producer
emitted is admitted by the checked reader, at the same program and the same recorded type,
once the host supplies the bindings its prelude provides. `printModule_roundTrip` is its
projection through the raw reader, and keeps its own statement. Source annotations beyond
the declaration's, nominal service requirements, the meaning of the `effect` package, and
target typing or execution remain separate obligations.
-/

namespace Effect4.Api

open Effect4.Program

/-- The public original-source check returns evidence exactly on the lexical
profile proved by SourceBindings, before core reconstruction erases metadata. -/
theorem checkSourceBindings_iff (module : TypeScript.Module)
    (allowed : List Effect4.Codegen.Bindings.Origin) :
    (∃ checked, checkSourceBindings module allowed = some checked) ↔
      Effect4.Codegen.SourceBindings.WellBound allowed module :=
  Effect4.Codegen.SourceBindings.validate_iff allowed module

/-- The shared certificate exposes precisely the existing application type result. -/
theorem checkTyping_type (program : Program) (table : RowTable) :
    (checkTyping program table).map TypedProgram.ty = typeOf program table :=
  checkTypedProgram_type _ _

/-- Evidence retention does not alter any prior module output or refusal. -/
theorem printModule_erasure (name : String) (program : Program) (table : RowTable) :
    printModule name program table =
      match typeOf program table with
      | some ty =>
        match Effect4.Program.printEntry table (nativeSignature table) name ty program with
        | .ok decls => some { header := [], imports := [], decls := decls.map .const }
        | .error _ => none
      | none => none :=
  Effect4.Codegen.emitModule_erasure name program table

/-- Evidence retention also leaves the declaration interface unchanged. -/
theorem printDecl_erasure (name : String) (program : Program) (table : RowTable) :
    printDecl name program table =
      match typeOf program table, print program table with
      | some ty, .ok body => (Effect4.Program.printDecl name ty body).toOption
      | _, _ => none := by
  cases checked : checkTypedProgram (nativeSignature table) program with
  | none =>
    have typed := checkTypedProgram_refusal_iff.mp checked
    cases body : print program table <;>
      simp [printDecl, checkTyping, checked, typeOf, typed, body]
  | some typing =>
    cases body : print program table <;>
      simp [printDecl, checkTyping, checked, typeOf, typing.typed, body]

/-- O3 through the application face: an admitted module's program carries the type the
certificate records, by the one whole-program checker the rest of the tree uses. -/
theorem admitModule_typed {name : String} {module : TypeScript.Module} {table : RowTable}
    {allowed : List Effect4.Codegen.Bindings.Origin} {ambient : List TypeScript.Import}
    {r : Effect4.Codegen.ModuleReading table name allowed ambient}
    (admitted : admitModule name module table allowed ambient = .ok r) :
    typeOf r.program table = some r.typing.ty :=
  Effect4.Codegen.admitModule_typed admitted

/-- The certificate round trip through the application face: the module the checked
producer emitted, when it reads back to its program, is admitted by the checked
reader, at the same program and the same recorded type, once the embedding host's ambient
bindings are supplied. Nothing here claims the host's `effect` namespace is the pinned one. -/
theorem admitModule_emitModule {name : String} {program : Program} {table : RowTable}
    {e : Effect4.Codegen.ModuleEmission program table name}
    (_ : emitModule name program table = .ok e)
    (read : readModule e.module table = .ok program)
    {allowed : List Effect4.Codegen.Bindings.Origin} {ambient : List TypeScript.Import}
    (bound : Effect4.Codegen.SourceBindings.Checked allowed
      (Effect4.Codegen.withAmbient ambient e.module)) :
    ∃ r, admitModule name e.module table allowed ambient = .ok r ∧
      r.program = program ∧ r.typing.ty = e.typing.ty :=
  Effect4.Codegen.ModuleEmission.admit e read bound

end Effect4.Api
