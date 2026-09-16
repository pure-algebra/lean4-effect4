import Effect4.Program.CheckedTyping
import Effect4.Program.Native
import Effect4.Codegen.Print

/-!
# Checked module production

The existing program checker owns the inferred type. An emission retains that
check and the exact relation between this program, table, requested name and the
existing declaration printer. The module syntax is a projection of those retained
declarations, so a caller cannot replace an annotation independently of its receipt.

This certifies production, not source admission. The current raw printer still
omits annotations for nonempty requirements and supplies no imports. Original
source declarations and bindings must be validated at a separate reading boundary.
Target type checking and execution are not consequences of this certificate.
-/

namespace Effect4.Codegen

open Effect4.Program

/-- Failure to type the input, or the existing printer's precise refusal. -/
inductive EmissionRefusal where
  | illTyped
  | print (why : PrintRefusal)
  deriving DecidableEq, Repr

/-- A module's declarations and the checks that produced them from exactly the
indexed program, table and name. The only type evidence is `TypedProgram`.
There are no runner-only registration conditions at the code generation boundary. -/
structure ModuleEmission (program : NativeEff) (table : RowTable) (name : String) where
  typing : TypedProgram (nativeSignature table) program
  declarations : List TypeScript.ConstDecl
  generated : Program.printEntry table (nativeSignature table) name typing.ty program =
    .ok declarations

/-- The unchanged current module envelope, constructed from retained declarations.
Empty imports are an explicit limit of this producer, not evidence of source binding. -/
def ModuleEmission.module (emission : ModuleEmission program table name) : TypeScript.Module :=
  { header := [], imports := [], decls := emission.declarations.map .const }

/-- Emit from a checked input without accepting an independently supplied `EffTy`.
This worker does not rerun the checker or impose the runner's row restrictions. -/
def emitTypedModule (name : String) {program : NativeEff} {table : RowTable}
    (typing : TypedProgram (nativeSignature table) program) :
    Except EmissionRefusal (ModuleEmission program table name) :=
  match printed : Program.printEntry table (nativeSignature table) name typing.ty program with
  | .error why => .error (.print why)
  | .ok declarations => .ok ⟨typing, declarations, printed⟩

/-- Check once, then retain the successful check and the actual printer result.
Raw expression printing remains available for diagnostics and negative corpora. -/
def emitModule (name : String) (program : NativeEff) (table : RowTable := []) :
    Except EmissionRefusal (ModuleEmission program table name) :=
  match checkTypedProgram (nativeSignature table) program with
  | none => .error .illTyped
  | some typing => emitTypedModule name typing

end Effect4.Codegen
