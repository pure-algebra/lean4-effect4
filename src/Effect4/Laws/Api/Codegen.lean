import Effect4.Api
import Effect4.Laws.Codegen.Checked
import Effect4.Laws.Codegen.SourceBindings

/-!
# The application module face on its readable, typed domain

Compose the shared-layer syntax laws through the actual API. Type checking supplies
reference validity, the codegen table supplies spelling hygiene, and readability is
the exact-image premise. No successful output is assumed. This is a theorem about
the module AST returned by the existing API, not validation of a source annotation
or of the currently empty import envelope, and not host typing or execution.
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

/-- A typed readable program under a lawful codegen table has an API module whose
reading is the original program, including its explicit layer-sharing references.
The emitted declaration type must have a structural target reading; arbitrary
legacy handle strings do not follow from core typing alone. -/
theorem printModule_roundTrip (name : String) (program : Program) (table : RowTable)
    (lawful : LawfulTable table = true) {ty : EffTy}
    (typed : typeOf program table = some ty) (hr : readable program table = true)
    (types : declarationTypeRepresentable ty = true) :
    ∃ module, printModule name program table = some module ∧
      readModule module table = .ok program := by
  let typing : TypedProgram (nativeSignature table) program := ⟨ty, typed⟩
  obtain ⟨emission, emitted⟩ := Effect4.Codegen.emitModule_complete
    (name := name) typing lawful hr types
  exact ⟨emission.module,
    by simp only [printModule, emitted, Except.toOption, Option.map],
    emission.readModule lawful hr⟩

end Effect4.Api
