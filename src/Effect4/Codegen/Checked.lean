import Effect4.Program.Formation
import Effect4.Program.CheckedTyping
import Effect4.Program.Native
import Effect4.Program.Profile
import Effect4.Codegen.Print
import Effect4.Codegen.PrintTyped
import Effect4.Codegen.RowServices
import Effect4.Codegen.SourceBindings

/-!
# Checked module production

The existing program checker owns the inferred type. An emission retains that
check and the exact relation between this program, table, requested name and the
existing declaration printer. The module syntax is a projection of those retained
declarations, so a caller cannot replace an annotation independently of its receipt.

The declarations are the module that ships: its program pieces printed by the typed print, which
writes a call's type arguments where a join needs them, or by the table's fold where the typed
print refuses (`shippedPieces`; decisions row 373 (11)).
The reading boundary reads them after the named erasure of those arguments (`readModuleTyped`).

This certifies production, not source admission. The printer retains all three type parameters.
The envelope `module` supplies no imports: an embedding host prepends its own. The file
`ModuleEmission.file` writes the imports from Lean data (decisions row 373 (11)). Original
source declarations and bindings must be validated at a separate reading boundary.
Target type checking and execution are not consequences of this certificate.
-/

namespace Effect4.Codegen

open Effect4.Program

-- `Program.table` (the address table) is in scope through the typed print; the emission's
-- indices are named here so that `table` is the row table.
variable {program : NativeEff} {table : RowTable} {name : String}

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
  generated : Program.printEntryWith Program.shippedPieces table (nativeSignature table) name
    typing.ty program = .ok declarations

/-- The module envelope, constructed from retained declarations: the payload classes first,
then the declaration block. Empty imports are an explicit limit of this producer, not evidence
of source binding. -/
def ModuleEmission.module (emission : ModuleEmission program table name) : TypeScript.Module :=
  { header := [], imports := []
    decls := emission.classDecls.map .classDecl ++ emission.declarations.map .const }

/-! ## The module as a file: its imports from Lean data (decisions row 373 (11))

The envelope `module` is the declaration block that an embedding host wraps: it holds no import,
and the host prepends its own (`withAmbient`, `Codegen/Admit.lean`). An agent's file needs its
imports written, and its row namespaces declared. `file` declares each row namespace that is an
Effect service (`rowServiceDecls`, `Codegen/RowServices.lean`; decisions row 378 (19)) after the
payload classes and before the declarations that call it. It writes the imports from Lean data:
the module's free names, by the binding analysis (`SourceBindings.moduleUses`), each from
`effect` when it is one of `effect`'s names and from the prelude when it is a prelude name. Any
other free name stays free: a row that is no service row is the host's. Every declaration is
exported already (`ConstDecl.exported`), the service key, its layer and the main among them. -/

/-- The names a printed module may import from its prelude: the atoms, the term helpers, the
number tower's aliases (`Types.typeAliasNames`), and the printer's heads that are no namespace
member, except `pipe` and `undefined`. A head is a namespace
member when its spelling holds a dot. The test reads bytes (`46` is `.`), since the string
API's character traversals reach `Classical.choice` on this toolchain. -/
def preludeNames : List String :=
  NativeAtom.names ++ termHelperNames ++ Types.typeAliasNames ++
    reserved.filter fun h => !h.toUTF8.data.toList.contains 46 && h != "pipe" && h != "undefined"

/-- Whether a name comes from `effect`: one of its namespaces (`effectNamespaces`), or its root
export `pipe`. -/
def fromEffect (name : String) : Bool := effectNamespaces.contains name || name == "pipe"

/-- The free names of a module: each name that a use reads and no binding of the module resolves,
once, in the order of first use, with whether every use of it is a type. -/
def freeNames (module : TypeScript.Module) : List (String × Bool) :=
  let uses := (SourceBindings.moduleUses module).uses.filter fun u => !SourceBindings.useResolved u
  uses.foldl (fun acc u =>
    let typeOnly := u.space == .type
    match acc.find? (·.1 == u.name) with
    | some _ => acc.map fun (n, t) => if n == u.name then (n, t && typeOnly) else (n, t)
    | none => acc ++ [(u.name, typeOnly)]) []

/-- Byte order: lexicographic on UTF-8 bytes, which is the order of code points. -/
def bytesLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else bytesLe as bs

/-- **A module's imports, from Lean data** (decisions row 373 (11)). The free names of `effect` come
from `effect`, then the free prelude names from `prelude`, each list in byte order. A binding is
type-only when every use of its name is a type. A name in `except` is no import: a hole, which
the host answers until it is filled. A free name of neither stays free. -/
def moduleImports (prelude : String) (module : TypeScript.Module) (except : List String := []) :
    List TypeScript.Import :=
  let free := ((freeNames module).mergeSort fun a b =>
      bytesLe a.1.toUTF8.data.toList b.1.toUTF8.data.toList).filter fun p => !except.contains p.1
  let binding (p : String × Bool) : TypeScript.ImportBinding :=
    { imported := p.1, localName := p.1, typeOnly := p.2 }
  let ofEffect := free.filter fun p => fromEffect p.1
  let ofPrelude := free.filter fun p => !fromEffect p.1 && preludeNames.contains p.1
  (if ofEffect.isEmpty then [] else [.named (ofEffect.map binding) "effect" false]) ++
    (if ofPrelude.isEmpty then [] else [.named (ofPrelude.map binding) prelude false])

/-- A module as a file: its declarations, with the imports that their free names need
(`moduleImports`), the prelude at `prelude`. The new imports replace any that the module held. A
name in `except` is no import. -/
def fileOf (prelude : String) (module : TypeScript.Module) (except : List String := []) :
    TypeScript.Module :=
  { module with imports := moduleImports prelude { module with imports := [] } except }

/-- **The module as a file**: the payload classes, the row namespaces' services
(`rowServiceDecls`), then the envelope's declarations, with their imports (`fileOf`), the prelude
at `prelude`. Refused by a row's spelling where the rows' services do not print. The read-back
law (`ModuleEmission.readModule`, `src/Effect4/Laws/Api/ModuleReadable.lean`) speaks of the
envelope's declarations, which the file holds after the rows' services. -/
def ModuleEmission.file (emission : ModuleEmission program table name) (prelude : String)
    (except : List String := []) : Except PrintRefusal TypeScript.Module := do
  let rows ← rowServiceDecls (nativeSignature table) table
  pure (fileOf prelude { emission.module with
    decls := emission.classDecls.map .classDecl ++ rows.map .const ++
      emission.declarations.map .const } except)

/-- **A module of a program that is not checked**: the program printed plain, one exported
`const name = …` with no declared type, and its imports from Lean data (`fileOf`), the prelude at
`prelude`; a name in `except` is no import. A lane that shows what a host makes of an ill-typed
program prints it so, with the writer every lane uses (decisions row 392, P1 (a)). A checked
program's module is its emission's `file`. -/
def uncheckedFile (prelude : String) (name : String) (program : NativeEff) (table : RowTable := [])
    (except : List String := []) : Except PrintRefusal TypeScript.Module := do
  let x ← Program.print (nativeSignature table) 0 program
  pure (fileOf prelude { header := [], imports := [], decls := [.const { doc := [], name, value := x }] }
    except)

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
    match printed : Program.printEntryWith Program.shippedPieces table (nativeSignature table) name
        typing.ty program with
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
