import Effect4.Api
import Effect4.Laws.Codegen.Module

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

/-- A typed readable program under a lawful codegen table has an API module whose
reading is the original program, including its explicit layer-sharing references. -/
theorem printModule_roundTrip (name : String) (program : Program) (table : RowTable)
    (lawful : LawfulTable table = true) {ty : EffTy}
    (typed : typeOf program table = some ty) (hr : readable program table = true) :
    ∃ module, printModule name program table = some module ∧
      readModule module table = .ok program := by
  have valid : program.layerRefsWF = true := by
    cases h : program.layerRefsWF with
    | false => simp [typeOf, Effect4.Program.typeOfProgram, h] at typed
    | true => rfl
  obtain ⟨decls, printed⟩ := Effect4.Program.printModule_readable hr valid name ty
  have safe : table.find? (fun row => !rowNamesSafe row) = none := by
    apply List.find?_eq_none.mpr
    intro row mem
    have h := (lawfulTable_member table lawful row mem).2.2
    simp [h]
  refine ⟨{ header := [], imports := [], decls := decls.map .const }, ?_, ?_⟩
  · simp only [printModule, typed, Effect4.Program.printEntry, safe, printed]
  · exact Effect4.Program.readModule_printModule_readable
      (nativeLawful table lawful) hr valid printed

end Effect4.Api
