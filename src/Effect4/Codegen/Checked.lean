import Effect4.Program.Formation
import Effect4.Program.CheckedTyping
import Effect4.Program.Native
import Effect4.Codegen.Print

/-!
# Checked module production

The existing program checker owns the inferred type. An emission retains that
check and the exact relation between this program, table, requested name and the
existing declaration printer. The module syntax is a projection of those retained
declarations, so a caller cannot replace an annotation independently of its receipt.

This certifies production, not source admission. The printer retains all three type parameters but supplies no imports. Original
source declarations and bindings must be validated at a separate reading boundary.
Target type checking and execution are not consequences of this certificate.
-/

namespace Effect4.Codegen

open Effect4.Program

/-- Failure to type the input, or the existing printer's precise refusal. -/
inductive EmissionRefusal where
  | illTyped
  | print (why : PrintRefusal)
  | formation (why : Formation.Refusal)
  deriving DecidableEq, Repr

/-- A module's declarations and the checks that produced them from exactly the
indexed program, table and name. `formed` records raw formation; `typing` records
the ordinary core typing judgment.
There are no runner-only registration conditions at the code generation boundary. -/
structure ModuleEmission (program : NativeEff) (table : RowTable) (name : String) where
  formed : Formation.InputFormed program table
  typing : TypedProgram (nativeSignature table) program
  declarations : List TypeScript.ConstDecl
  generated : Program.printEntry table (nativeSignature table) name typing.ty program =
    .ok declarations

/-- The unchanged current module envelope, constructed from retained declarations.
Empty imports are an explicit limit of this producer, not evidence of source binding. -/
def ModuleEmission.module (emission : ModuleEmission program table name) : TypeScript.Module :=
  { header := [], imports := [], decls := emission.declarations.map .const }

/-- Print from retained typing and raw formation evidence. Both public producers
obtain this evidence before calling the declaration printer. -/
def emitFormedModule (name : String) {program : NativeEff} {table : RowTable}
    (formed : Formation.InputFormed program table)
    (typing : TypedProgram (nativeSignature table) program) :
    Except EmissionRefusal (ModuleEmission program table name) :=
  match printed : Program.printEntry table (nativeSignature table) name typing.ty program with
  | .error why => .error (.print why)
  | .ok declarations => .ok ⟨formed, typing, declarations, printed⟩

/-- A typing certificate does not replace raw formation. Check it before printing. -/
def emitTypedModule (name : String) {program : NativeEff} {table : RowTable}
    (typing : TypedProgram (nativeSignature table) program) :
    Except EmissionRefusal (ModuleEmission program table name) :=
  match hformed : Formation.checkInput program table with
  | some why => .error (.formation why)
  | none => emitFormedModule name
      ((Formation.checkInput_eq_none_iff program table).mp hformed) typing

/-- Check raw formation before the type checker can normalize the input. -/
def emitModule (name : String) (program : NativeEff) (table : RowTable := []) :
    Except EmissionRefusal (ModuleEmission program table name) :=
  match hformed : Formation.checkInput program table with
  | some why => .error (.formation why)
  | none =>
    match checkTypedProgram (nativeSignature table) program with
    | none => .error .illTyped
    | some typing => emitFormedModule name
        ((Formation.checkInput_eq_none_iff program table).mp hformed) typing

end Effect4.Codegen
