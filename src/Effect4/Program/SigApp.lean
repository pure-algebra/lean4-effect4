import Effect4.Program.Columns
import Effect4.Program.Table
import Effect4.Program.TyDecls

/-!
# Program.SigApp — Σ_app: the application's part of the signature, and its located refusal

Decisions rows 111–116 (ruled 2026-10-01). The open part of the signature is Σ_app: the host-row
table, the application's service declarations and its named types (`SigApp`). The core alphabet (`NativeOp`,
`SyncOp`, `FiberOp`, the atoms) stays fixed and grows only under DI-47's finite gate.

* **The signature an application's tables give the checker** (`SigApp.signature`). Service
  carriers are per code (row 113; `Machine/Key.lean`'s `carrier_def`: "selection is by the
  code, never by the nominal name"): the reserved `Scope` key keeps its exception, the machine's
  reserved names type nothing, and a free name's code reads the application's declarations
  before the built-in codes. With no declarations it is `nativeSignature`.
* **Its located refusal** (`admitSig`): every row meets its local checks (`rowChecks`: the
  runner's registration, the program-plane table conditions, the three column scans of
  `Program/Columns.lean` at the root, and the template profile), the row keys are distinct, every
  declaration meets its local checks (`serviceChecks`, row 114), the declared codes are distinct
  (row 113), and every key a row requires has a carrier. Then the application's named types
  (`types`, decisions rows 401 and 402): each declaration meets its local checks (`declChecks`),
  each row spells every name with one meaning under the table (`nameChecks`, decisions row 406
  (1)), no name has two bodies, and the table is guarded. Program admission runs it (`admitProgram`,
  `Program/Admission.lean`).

The theorems live in `Laws/Program/Signature.lean`: the refusal is complete against `LawfulSig`
(`admitSig_ok_iff`), extension and restriction, and the projections program admission's consumers
read. This module is not a Lean module (decisions row 200): it imports `Program/Columns.lean`,
which imports one of decisions row 202's specialization sites.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey ServiceTypeCode)

/-- The application's part of the signature (row 111): the host-row table, the service
declarations, each a key and its carrier, and the declaration table of the application's named
types (decisions rows 401 and 402). -/
structure SigApp where
  rows : RowTable := []
  services : List (ServiceKey × Ty) := []
  types : TyDecls := []

namespace SigApp

/-- The signature of a row table alone: no service declaration and no named type. -/
def ofTable (rows : RowTable) : SigApp := { rows }

/-- The carrier the application declares for a service code: its first declaration there. -/
def codeTy (app : SigApp) (code : ServiceTypeCode) : Option Ty :=
  (app.services.find? (fun entry => entry.1.service == code)).map Prod.snd

/-- The carrier the built-in table gives a service code. -/
def builtinCodeTy (code : ServiceTypeCode) : Option Ty :=
  (nativeServiceTypes.find? (fun entry => entry.1 == code.value)).map Prod.snd

/-- A key's carrier under the application's signature, selected by its code (row 113): the
reserved `Scope` key keeps its exception, the machine's reserved names type nothing, and a
free name's code reads the application's declarations before the built-in codes. -/
def serviceTy (app : SigApp) (key : ServiceKey) : Option Ty :=
  match nativeReservedServiceTypes.find? (fun entry => entry.1 == key) with
  | some (_, ty) => some ty
  | none =>
    if key.name.value < Effect4.Machine.Env.firstFreeName then none
    else match app.codeTy key.service with
      | some ty => some ty
      | none => builtinCodeTy key.service

/-- The checker's signature over an application's tables: its rows and its service carriers. It
declares no named type, so the term typer reads every declared name as a handle, and program
admission and the typed state (M5 to M7) read the checker as before. -/
def signature (app : SigApp) : Signature NativeOp :=
  { nativeSignature app.rows with serviceTy := app.serviceTy }

/-- **The checker's signature under the application's named types**: `signature` with the
declaration table, which the term typer reads (`Signature.types`; the wiring plan,
`docs/research/2026-10-16-usability-scope/wiring-plan.md`). At an application with no named type
it is `signature`. The typed state's guarantee is claimed at `signature` only (the plan's
decision 5). -/
def signatureIn (app : SigApp) : Signature NativeOp :=
  { app.signature with types := app.types }

end SigApp

/-- A row is well scoped when every parameter its answer or its error mentions is one its
request binds. `infer` reads bindings from the request alone (`rowTy`), so a parameter that
appeared only on an answer would be instantiated at nothing and printed back as a `var`. -/
def Row.wellScoped (row : Row) : Bool :=
  (row.answer.varsOf ++ row.error.varsOf).all fun i => row.request.varsOf.contains i

/-- A row's local conditions, with the reason each one gives when it fails. -/
inductive RowReason
  /-- `checkTable`: the runner registers only external rows. -/
  | notExternal
  /-- `checkTable`: only asynchronous rows. -/
  | notAsync
  /-- `Table.lawful`: the row's key collides with a built-in spelling key (`builtinKeys`). -/
  | builtinCollision
  /-- `Table.lawful`: a value row has trailing names. -/
  | valueRowTrailing
  /-- Row 97: the answer or error column mentions an internal handle kind. -/
  | internalHandle (column : String)
  /-- Row 127: the column is empty and is not `never`, with every template parameter read as
  inhabited (row 155 (a), `admitRowColumn`). -/
  | emptyColumn (column : String)
  /-- Row 42: a template parameter sits under a union in the column. -/
  | templateNotAdmissible (column : String)
  /-- Row 42: the answer or error names a parameter the request does not bind. -/
  | notWellScoped
deriving DecidableEq, Repr

/-- A row's local checks, in the order a refusal names the first failing one. -/
def rowChecks (r : Row) : List (Bool × RowReason) :=
  [(r.registration == .external, .notExternal),
   (r.kind == .async, .notAsync),
   (!builtinKeys.contains (rowKey r), .builtinCollision),
   (!(r.shape == .value) || r.trailing.isEmpty, .valueRowTrailing),
   ((findInternalHandle [] r.answer).isNone, .internalHandle "answer"),
   ((findInternalHandle [] r.error).isNone, .internalHandle "error"),
   (admitRowColumn r.request, .emptyColumn "request"),
   (admitRowColumn r.answer, .emptyColumn "answer"),
   (admitRowColumn r.error, .emptyColumn "error"),
   (r.request.templateAdmissible, .templateNotAdmissible "request"),
   (r.answer.templateAdmissible, .templateNotAdmissible "answer"),
   (r.error.templateAdmissible, .templateNotAdmissible "error"),
   (r.wellScoped, .notWellScoped)]

/-- A declaration's local conditions (row 114), with their reasons. -/
inductive ServiceReason
  /-- The key's name is one the machine reserves (`Env.firstFreeName`). -/
  | reservedName
  /-- The carrier is not flat (`unit`, `nat`, `bool`, `string`, a handle that is neither the
  context nor a mask's saved state). -/
  | nonFlatCarrier
  /-- The built-in table gives the key's code another carrier. -/
  | conflictsBuiltin
deriving DecidableEq, Repr

/-- The flat carriers, as a fold: the scalars, every handle but the context and the mask's saved
state, and a cell. The saved state is refused in the first profile (decisions row 244): its image
is no handle frame, so `FlatFits` has no member at its type, and a service that carried it would
need the membership of a context's services at the type. -/
def flatCarrierAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := false
  ty_string := true
  ty_bool := true
  ty_handle target := target != Ty.contextTarget && target != Ty.maskRestoreTarget
  ty_option _ := false
  ty_list _ := false
  ty_prod _ _ := false
  ty_except _ _ := false
  ty_exitOf _ _ := false
  ty_causeOf _ := false
  ty_fiberOf _ _ := false
  ty_union _ _ := false
  ty_lit _ := false
  -- a cell's membership reads the world's table at its argument, with no recursion into it, so
  -- `refOf t` is flat at every `t` (service code 7 is `refOf nat`, the state plan's T3a)
  ty_refOf _ := true
  ty_deferredOf _ _ := false
  ty_var _ := false
  ty_unknown := false
  -- structured carriers are row 118's; the data wave's leaves are not service carriers yet
  ty_record _ := false
  ty_map _ _ := false
  ty_tuple _ := false
  ty_app _ _ := false
  ty_null := false
  ty_undefined := false
  ty_number := false
  ty_bytes := false
  ty_contextOf _ := false

/-- A flat carrier (row 114; row 118 owns structured carriers): the scalars, a handle that is
neither the context nor a mask's saved state (row 244), and a cell at any type. -/
def flatCarrier (t : Ty) : Bool := cata_ty flatCarrierAlg t

/-- A declaration's local checks, in order. -/
def serviceChecks (e : ServiceKey × Ty) : List (Bool × ServiceReason) :=
  [(decide (Effect4.Machine.Env.firstFreeName ≤ e.1.name.value), .reservedName),
   (flatCarrier e.2, .nonFlatCarrier),
   ((SigApp.builtinCodeTy e.1.service).all (· == e.2), .conflictsBuiltin)]

/-- The names a type applies to arguments: each `app n args` with arguments, anywhere in it. -/
def appliedAlg : TyAlgebra (fun _ => List String) where
  ty_never := []
  ty_unit := []
  ty_nat := []
  ty_int := []
  ty_string := []
  ty_bool := []
  ty_handle _ := []
  ty_option m := m
  ty_list m := m
  ty_prod a b := a ++ b
  ty_except a b := a ++ b
  ty_exitOf a b := a ++ b
  ty_causeOf m := m
  ty_fiberOf a b := a ++ b
  ty_union a b := a ++ b
  ty_lit _ := []
  ty_refOf m := m
  ty_deferredOf a b := a ++ b
  ty_var _ := []
  ty_unknown := []
  ty_record fs := (fs.map fun f => f.2.2).flatten
  ty_map a b := a ++ b
  ty_tuple ms := ms.flatten
  ty_app n args := (if args.isEmpty then [] else [n]) ++ args.flatten
  ty_null := []
  ty_undefined := []
  ty_number := []
  ty_bytes := []
  ty_contextOf _ := []

/-- The names a type applies to arguments (`appliedAlg`). -/
def Ty.appliedNames (t : Ty) : List String := cata_ty appliedAlg t

/-- The names a type spells, anywhere in it: each host handle `handle n` as `(true, n)`, and each
reference with no argument `app n []` as `(false, n)` (decisions row 406 (1)). -/
def spelledAlg : TyAlgebra (fun _ => List (Bool × String)) where
  ty_never := []
  ty_unit := []
  ty_nat := []
  ty_int := []
  ty_string := []
  ty_bool := []
  ty_handle n := [(true, n)]
  ty_option m := m
  ty_list m := m
  ty_prod a b := a ++ b
  ty_except a b := a ++ b
  ty_exitOf a b := a ++ b
  ty_causeOf m := m
  ty_fiberOf a b := a ++ b
  ty_union a b := a ++ b
  ty_lit _ := []
  ty_refOf m := m
  ty_deferredOf a b := a ++ b
  ty_var _ := []
  ty_unknown := []
  ty_record fs := (fs.map fun f => f.2.2).flatten
  ty_map a b := a ++ b
  ty_tuple ms := ms.flatten
  ty_app n args := (if args.isEmpty then [(false, n)] else []) ++ args.flatten
  ty_null := []
  ty_undefined := []
  ty_number := []
  ty_bytes := []
  ty_contextOf _ := []

/-- The names a type spells (`spelledAlg`). -/
def Ty.spelledNames (t : Ty) : List (Bool × String) := cata_ty spelledAlg t

/-- The names a row's three columns spell. -/
def Row.spelledNames (r : Row) : List (Bool × String) :=
  r.request.spelledNames ++ r.answer.spelledNames ++ r.error.spelledNames

/-- A declaration's local conditions (decisions row 401 (2)), with their reasons. -/
inductive DeclReason
  /-- The name is an internal handle's spelling (`internalHandleTargets`): one spelling, one
  meaning. -/
  | internalSpelling
  /-- The body has a type variable: a declaration is monomorphic. -/
  | typeVariable
  /-- The body applies a declared name to arguments: a declared name takes none. -/
  | applied
  /-- A host handle `handle n` at a name the table declares: one spelling, one meaning (decisions
  row 406 (1)). -/
  | handleAtName
  /-- A reference with no argument `app n []` at a name the table does not declare. -/
  | undeclaredName
deriving DecidableEq, Repr

/-- The checks on the names a type or a row spells, against the table (decisions row 406 (1)):
no host handle at a declared name, and no reference with no argument at an undeclared one. -/
def nameChecks (decls : TyDecls) (names : List (Bool × String)) : List (Bool × DeclReason) :=
  [(names.all fun s => !s.1 || (decls.body? s.2).isNone, .handleAtName),
   (names.all fun s => s.1 || (decls.body? s.2).isSome, .undeclaredName)]

/-- A declaration's local checks, in order, against the table it sits in. -/
def declChecks (decls : TyDecls) (d : String × Ty) : List (Bool × DeclReason) :=
  [(!internalHandleTargets.contains d.1, .internalSpelling),
   (d.2.varsOf.isEmpty, .typeVariable),
   ((d.2.appliedNames.filter fun n => (decls.body? n).isSome).isEmpty, .applied)] ++
  nameChecks decls d.2.spelledNames

/-- The first name a table declares with two different bodies (decisions row 402 (5)): a
repeated entry is one declaration, two bodies at one name are two meanings. -/
def firstConflict : TyDecls → Option String
  | [] => none
  | d :: rest => if rest.any (fun e => e.1 == d.1 && e.2 != d.2) then some d.1
    else firstConflict rest

/-- The first failing check's reason. -/
def firstFailing {β : Type} (checks : List (Bool × β)) : Option β :=
  (checks.find? fun c => !c.1).map Prod.snd

/-- The first position of a list whose element a check refuses, with the refusal. -/
def firstIndexed {α β : Type} (f : α → Option β) : Nat → List α → Option (Nat × β)
  | _, [] => none
  | i, x :: xs =>
    match f x with
    | some b => some (i, b)
    | none => firstIndexed f (i + 1) xs

/-- The first repeated element of a list. -/
def firstDup {α : Type} [DecidableEq α] : List α → Option α
  | [] => none
  | x :: xs => if x ∈ xs then some x else firstDup xs

/-- Why a signature is not lawful, located: a row by its position, a declaration by its
position, a repeated row key or service code, a required key with no carrier; a named type's
declaration by its position, a row that spells a name with two meanings or none, a name with two
bodies, a name the ranking leaves unranked. -/
inductive SigRefusal
  | row (index : Nat) (reason : RowReason)
  | duplicateRow (key : String × List RowArg)
  | service (index : Nat) (reason : ServiceReason)
  | duplicateCode (code : ServiceTypeCode)
  | unservedKey (row : Nat) (key : ServiceKey)
  | decl (index : Nat) (reason : DeclReason)
  | rowName (index : Nat) (reason : DeclReason)
  | conflictingDecl (name : String)
  | unguardedDecl (name : String)
deriving DecidableEq, Repr

/-- The first refusal, in the order rows, row keys, declarations, codes, required keys, then the
named types: each declaration, each row's spelled names, the names, the ranking. -/
def sigRefusal? (app : SigApp) : Option SigRefusal :=
  ((firstIndexed (fun r => firstFailing (rowChecks r)) 0 app.rows).map
      fun found => .row found.1 found.2).or <|
  ((firstDup (app.rows.map rowKey)).map .duplicateRow).or <|
  ((firstIndexed (fun e => firstFailing (serviceChecks e)) 0 app.services).map
      fun found => .service found.1 found.2).or <|
  ((firstDup (app.services.map (·.1.service))).map .duplicateCode).or <|
  ((firstIndexed (fun r => r.requires.find? fun k => !(app.serviceTy k).isSome) 0 app.rows).map
      fun found => .unservedKey found.1 found.2).or <|
  ((firstIndexed (fun d => firstFailing (declChecks app.types d)) 0 app.types).map
      fun found => .decl found.1 found.2).or <|
  ((firstIndexed (fun r => firstFailing (nameChecks app.types r.spelledNames)) 0 app.rows).map
      fun found => .rowName found.1 found.2).or <|
  ((firstConflict app.types).map .conflictingDecl).or <|
  app.types.unguardedAt?.map .unguardedDecl

/-- **Admit a signature**: a located refusal, or `ok`. -/
def admitSig (app : SigApp) : Except SigRefusal Unit :=
  match sigRefusal? app with
  | some why => .error why
  | none => .ok ()

end Effect4.Program
