import Effect4.Program.Formation
import Effect4.Program.CheckedTyping
import Effect4.Program.Native
import Effect4.Program.Profile
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
  /-- A natural literal above the TypeScript face's bound, rc.112's `Number.MAX_SAFE_INTEGER`:
  JavaScript would read it as another number (DI-56; `E4-PRINT-CE-002`). -/
  | outsideProfile (value : Nat)
  deriving DecidableEq, Repr

/-! ## The face's profile: the natural literals a program states -/

/-- The natural literals of a term, by the generated term fold. -/
def termNatLiterals (term : Term) : List Nat :=
  foldMap_term [] (· ++ ·) term (f_term := fun
    | .lit (.nat n) => [n]
    | _ => [])

/-- The natural literals of a cause, by the generated cause fold. -/
def causeNatLiterals (cause : CauseTerm) : List Nat :=
  cata_cause (R := fun _ => List Nat) {
    cause_fail := termNatLiterals
    cause_die := termNatLiterals
    cause_interrupt := fun who => who.toList.flatMap termNatLiterals
    cause_both := (· ++ ·) } cause

/-- The natural literals of one argument of the generated program view: a term, a cause, an
optional term, an operation's binder term, or a literal argument. -/
def argNatLiterals {Op : Type} [ScopedOp Op] : ArgF Op (EffSelfCarrier Op) → List Nat
  | .term term => termNatLiterals term
  | .cause cause => causeNatLiterals cause
  | .optTerm term => term.toList.flatMap termNatLiterals
  | .op op => (ScopedOp.term? op).toList.flatMap termNatLiterals
  | .lit (.nat n) => [n]
  | _ => []

/-- The natural literals of one program node, read through the generated view. -/
def nodeNatLiterals {Op : Type} [ScopedOp Op] (fam : EffFam) (node : EffSelfCarrier Op fam) :
    List Nat :=
  (view fam node).2.flatMap argNatLiterals

/-- Every natural literal a program states, by the generated program fold. -/
def natLiterals {Op : Type} [ScopedOp Op] (program : Eff Op) : List Nat :=
  foldMap_eff [] (· ++ ·) program
    (f_eff := nodeNatLiterals .eff) (f_stmt := nodeNatLiterals .stmt)
    (f_stmts := nodeNatLiterals .stmts) (f_effs := nodeNatLiterals .effs)
    (f_action := nodeNatLiterals .action) (f_layer := nodeNatLiterals .layer)
    (f_layers := nodeNatLiterals .layers)

/-- Every natural literal of the program is inside the TypeScript face's profile, so JavaScript
reads each one as the number the model holds. -/
def natLiteralsInProfile {Op : Type} [ScopedOp Op] (program : Eff Op) : Bool :=
  (natLiterals program).all (· ≤ rc112.natBound)

/-- A module's declarations and the checks that produced them from exactly the
indexed program, table and name. `formed` records raw formation; `typing` records
the ordinary core typing judgment; `inProfile` records that every natural literal is inside the
TypeScript face's bound (DI-56); `classified` records the payload classes the module
declares and their declarations (decisions row 120, `ClassTable.moduleClasses`).
There are no runner-only registration conditions at the code generation boundary. -/
structure ModuleEmission (program : NativeEff) (table : RowTable) (name : String) where
  formed : Formation.InputFormed program table
  typing : TypedProgram (nativeSignature table) program
  inProfile : natLiteralsInProfile program = true
  classes : Classes.Classes
  classDecls : List TypeScript.ClassDecl
  classified : ClassTable.moduleClasses (nativeSignature table) name typing.ty program =
    .ok (classes, classDecls)
  declarations : List TypeScript.ConstDecl
  generated : Program.printEntry table (nativeSignature table) name typing.ty program =
    .ok declarations

/-- The module envelope, constructed from retained declarations: the payload classes first,
then the declaration block. Empty imports are an explicit limit of this producer, not evidence
of source binding. -/
def ModuleEmission.module (emission : ModuleEmission program table name) : TypeScript.Module :=
  { header := [], imports := []
    decls := emission.classDecls.map .classDecl ++ emission.declarations.map .const }

/-- Print from retained typing and raw formation evidence. Both public producers
obtain this evidence before calling the declaration printer. -/
def emitFormedModule (name : String) {program : NativeEff} {table : RowTable}
    (formed : Formation.InputFormed program table)
    (typing : TypedProgram (nativeSignature table) program) :
    Except EmissionRefusal (ModuleEmission program table name) :=
  match inProfile : natLiteralsInProfile program with
  | false => .error (.outsideProfile
      (((natLiterals program).find? fun n => decide (rc112.natBound < n)).getD 0))
  | true =>
    match printed : Program.printEntry table (nativeSignature table) name typing.ty program with
    | .error why => .error (.print why)
    | .ok declarations =>
      match classified : ClassTable.moduleClasses (nativeSignature table) name typing.ty program with
      | .error why => .error (.print why)
      | .ok (classes, classDecls) =>
        .ok ⟨formed, typing, inProfile, classes, classDecls, classified, declarations, printed⟩

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
