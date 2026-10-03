import Effect4.Codegen.Checked
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Codegen.Module

/-!
# Certified production through the existing module algebra

The producer certificate is unique for its program/table/name. Erasing it gives
the previous printer interface on raw formed input.
Successful checking alone promises neither printing nor source validity. Adequacy
uses the established readable, lawful-spelling and representable-annotation domain;
reconstruction then follows from the existing hoist/restore and expression proofs.
-/

namespace Effect4.Codegen

open Effect4.Program

variable {program : NativeEff} {table : RowTable} {name : String}

/-- Retaining raw formation and typing evidence does not change successful printing. -/
theorem emitFormedModule_ok (formed : Formation.InputFormed program table)
    (typing : TypedProgram (nativeSignature table) program)
    {declarations : List TypeScript.ConstDecl}
    (printed : Program.printEntry table (nativeSignature table) name typing.ty program =
      .ok declarations) :
    emitFormedModule name formed typing = .ok ⟨formed, typing, declarations, printed⟩ := by
  unfold emitFormedModule
  split
  · rename_i why refused
    rw [printed] at refused
    cases refused
  · rename_i found result
    have same := Except.ok.inj (result.symm.trans printed)
    cases same
    rfl

/-- The typed entry still checks raw formation before printing (`raw-formation`). -/
theorem emitTypedModule_ok (formed : Formation.InputFormed program table)
    (typing : TypedProgram (nativeSignature table) program)
    {declarations : List TypeScript.ConstDecl}
    (printed : Program.printEntry table (nativeSignature table) name typing.ty program =
      .ok declarations) :
    emitTypedModule name typing = .ok ⟨formed, typing, declarations, printed⟩ := by
  unfold emitTypedModule
  split
  · rename_i why refused
    rw [(Formation.checkInput_eq_none_iff program table).mpr formed] at refused
    cases refused
  · exact emitFormedModule_ok formed typing printed

/-- A completed emission is exactly the result of the computed producer. -/
theorem ModuleEmission.recheck (emission : ModuleEmission program table name) :
    emitModule name program table = .ok emission := by
  cases emission with
  | mk formed typing declarations generated =>
    unfold emitModule
    split
    · rename_i why refused
      rw [(Formation.checkInput_eq_none_iff program table).mpr formed] at refused
      cases refused
    · rw [checkTypedProgram_eq_some typing]
      exact emitFormedModule_ok formed typing generated

/-- One fixed input has one emitted syntax and one retained typing receipt. -/
theorem ModuleEmission.unique (left right : ModuleEmission program table name) :
    left = right :=
  Except.ok.inj (left.recheck.symm.trans right.recheck)

/-- On raw formed input, erasure is the existing type-and-print interface.
Malformed raw input is now refused before normalization (rows 192 and 193). -/
theorem emitModule_erasure (name : String) (program : NativeEff) (table : RowTable)
    (formed : Formation.InputFormed program table) :
    (emitModule name program table).toOption.map (·.module) =
      match typeOfProgram (nativeSignature table) program with
      | some ty =>
        match Program.printEntry table (nativeSignature table) name ty program with
        | .ok decls => some { header := [], imports := [], decls := decls.map .const }
        | .error _ => none
      | none => none := by
  unfold emitModule
  split
  · rename_i why refused
    rw [(Formation.checkInput_eq_none_iff program table).mpr formed] at refused
    cases refused
  · cases checked : checkTypedProgram (nativeSignature table) program with
    | none =>
      have typed := checkTypedProgram_refusal_iff.mp checked
      simp only [typed, Except.toOption, Option.map_none]
    | some typing =>
      dsimp only
      rw [typing.typed]
      unfold emitFormedModule
      split
      · rename_i why printed
        simp only [printed, Except.toOption, Option.map_none]
      · rename_i declarations printed
        simp only [printed, Except.toOption, ModuleEmission.module, Option.map_some]

/-- On raw formed input, a core typing refusal remains distinguishable. -/
theorem emitModule_illTyped_iff (formed : Formation.InputFormed program table) :
    emitModule name program table = .error .illTyped ↔
      typeOfProgram (nativeSignature table) program = none := by
  unfold emitModule
  split
  · rename_i why refused
    rw [(Formation.checkInput_eq_none_iff program table).mpr formed] at refused
    cases refused
  · cases checked : checkTypedProgram (nativeSignature table) program with
    | none =>
      have typed := checkTypedProgram_refusal_iff.mp checked
      simp only [typed]
    | some typing =>
      dsimp only
      unfold emitFormedModule
      split <;> simp only [typing.typed, Except.error.injEq, reduceCtorEq]

/-- The same core typing judgment belongs to the emitted program's certificate.
This is the declarative program judgment, not a TypeScript judgment. -/
theorem ModuleEmission.hasTy (emission : ModuleEmission program table name) :
    Conform.Effect4.Typing.HasTy (nativeSignature table) [] program.expandRefs
      emission.typing.ty :=
  emission.typing.hasTy

end Effect4.Codegen
