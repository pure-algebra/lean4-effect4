import Effect4.Codegen.Checked
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Codegen.Module

/-!
# Certified production through the existing module algebra

The producer certificate is unique for its program/table/name. Erasing it gives
exactly the previous printer interface, including every existing refusal.
Successful checking alone promises neither printing nor source validity. Adequacy
uses the established readable, lawful-spelling and representable-annotation domain;
reconstruction then follows from the existing hoist/restore and expression proofs.
-/

namespace Effect4.Codegen

open Effect4.Program

variable {program : NativeEff} {table : RowTable} {name : String}

/-- Retaining evidence does not change the raw printer's successful output. -/
theorem emitTypedModule_ok (typing : TypedProgram (nativeSignature table) program)
    {declarations : List TypeScript.ConstDecl}
    (printed : Program.printEntry table (nativeSignature table) name typing.ty program =
      .ok declarations) :
    emitTypedModule name typing = .ok ⟨typing, declarations, printed⟩ := by
  unfold emitTypedModule
  split
  · rename_i why refused
    simp [refused] at printed
  · rename_i found result
    have same := Except.ok.inj (result.symm.trans printed)
    cases same
    rfl

/-- A completed emission is exactly the result of the computed producer. -/
theorem ModuleEmission.recheck (emission : ModuleEmission program table name) :
    emitModule name program table = .ok emission := by
  cases emission with
  | mk typing declarations generated =>
    simp only [emitModule, checkTypedProgram_eq_some typing]
    exact emitTypedModule_ok typing generated

/-- One fixed input has one emitted syntax and one retained typing receipt. -/
theorem ModuleEmission.unique (left right : ModuleEmission program table name) :
    left = right :=
  Except.ok.inj (left.recheck.symm.trans right.recheck)

/-- Forgetting the certificate is exactly the previous application's module
producer, for all inputs, including ill-typed programs and printer refusals.
No readability or table lawfulness premise hides a changed rejection. -/
theorem emitModule_erasure (name : String) (program : NativeEff) (table : RowTable) :
    (emitModule name program table).toOption.map (·.module) =
      match typeOfProgram (nativeSignature table) program with
      | some ty =>
        match Program.printEntry table (nativeSignature table) name ty program with
        | .ok decls => some { header := [], imports := [], decls := decls.map .const }
        | .error _ => none
      | none => none := by
  cases checked : checkTypedProgram (nativeSignature table) program with
  | none =>
    have typed := checkTypedProgram_refusal_iff.mp checked
    simp [emitModule, checked, typed, Except.toOption]
  | some typing =>
    rw [typing.typed]
    simp only [emitModule, checked, emitTypedModule]
    split <;> simp_all [Except.toOption, ModuleEmission.module]

/-- A core typing refusal remains distinguishable from a printer refusal. -/
theorem emitModule_illTyped_iff :
    emitModule name program table = .error .illTyped ↔
      typeOfProgram (nativeSignature table) program = none := by
  cases checked : checkTypedProgram (nativeSignature table) program with
  | none =>
    have typed := checkTypedProgram_refusal_iff.mp checked
    simp [emitModule, checked, typed, Except.toOption]
  | some typing =>
    simp only [emitModule, checked, emitTypedModule]
    split <;> simp [typing.typed]

private theorem safeTable (lawful : LawfulTable table = true) :
    table.find? (fun row => !rowNamesSafe row) = none := by
  apply List.find?_eq_none.mpr
  intro row mem
  have safe := (lawfulTable_member table lawful row mem).2.2
  simp [safe]

/-- Every checked program in the established printable domain produces a retained
emission. The export name is part of that domain: the entry printer refuses a name that
collides with a printed binder, a reserved head or a layer reference name.
Successful output is a conclusion, not a condition of this theorem. -/
theorem emitModule_complete (typing : TypedProgram (nativeSignature table) program)
    (safe : exportNameSafe name = true)
    (lawful : LawfulTable table = true)
    (readable : Program.readable (nativeSignature table) (nativeSpell table) 0 program = true)
    (types : declarationTypeRepresentable typing.ty = true) :
    ∃ emission, emitModule name program table = .ok emission := by
  obtain ⟨decls, printed⟩ := Program.printModule_readable readable
    typing.layerRefsWF name typing.ty types
  have generated : Program.printEntry table (nativeSignature table) name typing.ty program =
      .ok decls := by
    simpa [Program.printEntry, safe, safeTable lawful] using printed
  let emission : ModuleEmission program table name := ⟨typing, decls, generated⟩
  exact ⟨emission, emission.recheck⟩

/-- Reading the emitted declaration block recovers its indexed program under the
existing canonical readability and table premises. This reconstructs the same
sharing references; it does not execute their expansion or validate source imports. -/
theorem ModuleEmission.readModule (emission : ModuleEmission program table name)
    (lawful : LawfulTable table = true)
    (readable : Program.readable (nativeSignature table) (nativeSpell table) 0 program = true) :
    Program.readModule (nativeSignature table) (nativeSpell table) emission.module.decls =
      .ok program := by
  obtain ⟨_, _, printed⟩ := Program.printEntry_ok emission.generated
  exact Program.readModule_printModule_readable (nativeLawful table lawful)
    readable emission.typing.layerRefsWF printed

/-- The same core typing judgment belongs to the emitted program's certificate.
This is the declarative program judgment, not a TypeScript judgment. -/
theorem ModuleEmission.hasTy (emission : ModuleEmission program table name) :
    Conform.Effect4.Typing.HasTy (nativeSignature table) [] program.expandRefs
      emission.typing.ty :=
  emission.typing.hasTy

end Effect4.Codegen
