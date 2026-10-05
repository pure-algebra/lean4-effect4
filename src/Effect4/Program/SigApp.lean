import Effect4.Program.Columns
import Effect4.Program.Table

/-!
# Program.SigApp — Σ_app: the application's part of the signature, and its located refusal

Decisions rows 111–116 (ruled 2026-10-01). The open part of the signature is Σ_app: the host-row
table and the application's service declarations (`SigApp`). The core alphabet (`NativeOp`,
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
  (row 113), and every key a row requires has a carrier. Program admission runs it
  (`admitProgram`, `Program/Admission.lean`).

The theorems live in `Laws/Program/Signature.lean`: the refusal is complete against `LawfulSig`
(`admitSig_ok_iff`), extension and restriction, and the projections program admission's consumers
read. This module is not a Lean module (decisions row 200): it imports `Program/Columns.lean`,
which imports one of decisions row 202's specialization sites.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey ServiceTypeCode)

/-- The application's part of the signature (row 111): the host-row table and the service
declarations, each a key and its carrier. -/
structure SigApp where
  rows : RowTable := []
  services : List (ServiceKey × Ty) := []

namespace SigApp

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

/-- The checker's signature over an application's tables. -/
def signature (app : SigApp) : Signature NativeOp :=
  { nativeSignature app.rows with serviceTy := app.serviceTy }

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
  /-- DB-15: the column mentions the reserved integer type. -/
  | intType (column : String)
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
   ((findInt [] r.request).isNone, .intType "request"),
   ((findInt [] r.answer).isNone, .intType "answer"),
   ((findInt [] r.error).isNone, .intType "error"),
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
  /-- The carrier is not flat (`unit`, `nat`, `bool`, `string`, a non-context handle). -/
  | nonFlatCarrier
  /-- The built-in table gives the key's code another carrier. -/
  | conflictsBuiltin
deriving DecidableEq, Repr

/-- The flat carriers, as a fold: the scalars, every handle but the context, and a cell. -/
def flatCarrierAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := false
  ty_string := true
  ty_bool := true
  ty_handle target := target != Ty.contextTarget
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

/-- A flat carrier (row 114; row 118 owns structured carriers): the scalars, a non-context
handle, and a cell at any type. -/
def flatCarrier (t : Ty) : Bool := cata_ty flatCarrierAlg t

/-- A declaration's local checks, in order. -/
def serviceChecks (e : ServiceKey × Ty) : List (Bool × ServiceReason) :=
  [(decide (Effect4.Machine.Env.firstFreeName ≤ e.1.name.value), .reservedName),
   (flatCarrier e.2, .nonFlatCarrier),
   ((SigApp.builtinCodeTy e.1.service).all (· == e.2), .conflictsBuiltin)]

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
position, a repeated row key or service code, a required key with no carrier. -/
inductive SigRefusal
  | row (index : Nat) (reason : RowReason)
  | duplicateRow (key : String × List String)
  | service (index : Nat) (reason : ServiceReason)
  | duplicateCode (code : ServiceTypeCode)
  | unservedKey (row : Nat) (key : ServiceKey)
deriving DecidableEq, Repr

/-- The first refusal, in the order rows, row keys, declarations, codes, required keys. -/
def sigRefusal? (app : SigApp) : Option SigRefusal :=
  ((firstIndexed (fun r => firstFailing (rowChecks r)) 0 app.rows).map
      fun found => .row found.1 found.2).or <|
  ((firstDup (app.rows.map rowKey)).map .duplicateRow).or <|
  ((firstIndexed (fun e => firstFailing (serviceChecks e)) 0 app.services).map
      fun found => .service found.1 found.2).or <|
  ((firstDup (app.services.map (·.1.service))).map .duplicateCode).or <|
  (firstIndexed (fun r => r.requires.find? fun k => !(app.serviceTy k).isSome) 0 app.rows).map
      fun found => .unservedKey found.1 found.2

/-- **Admit a signature**: a located refusal, or `ok`. -/
def admitSig (app : SigApp) : Except SigRefusal Unit :=
  match sigRefusal? app with
  | some why => .error why
  | none => .ok ()

end Effect4.Program
