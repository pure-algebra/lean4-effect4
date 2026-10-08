import Effect4
import Effect4.Schema.Codec

/-! Probe MODS-11: Lean types tied to `Ty` by one fold and one deriving command.

- **The carrier fold.** `cata_ty` with an algebra into `Σ α : Type, Image α` gives every
  supported `Ty` its canonical Lean carrier and its exact embedding together. It reuses the
  generated algebra (`TyAlgebra`, `src/Effect4/Program/Fold.lean`) and the `Image` combinators
  (`src/Effect4/Store/Carrier/Image.lean`). An unsupported constructor goes to `Empty`, and a
  second fold names it.
- **The one new combinator**: `Image.record`, a record's frame of columns, exact by construction.
- **`Modeled α`**: a `Ty` and an equivalence between `α` and the `Ty`'s carrier. `Image.equiv`
  carries the exact embedding across, so an instance needs no law of its own beyond the two
  inverse equations.
- **`derive_modeled S`**: writes the instance of a structure from its fields, in canonical
  field order, with a spelling for each field.
- **Interop**: the derived `Ty` gives the TypeScript type (`Codegen.Types.ofTy`), the Effect
  Schema representation (`Ty.schema`) and the JSON codec (`Effect4.Schema.encode`/`decode`). -/

set_option autoImplicit false

open Lean Elab Command Term Meta
open Effect4 Effect4.Program Effect4.Store

namespace TyModel

/-! ## The record combinator -/

/-- The columns of a record frame: names, and the values of a carrier, exactly. -/
structure Columns (ρ : Type) where
  names : List String
  toVals : ρ → List Val
  ofVals : List Val → Option ρ
  ofVals_toVals : ∀ r, ofVals (toVals r) = some r
  ofVals_exact : ∀ {vs r}, ofVals vs = some r → vs = toVals r

def Columns.nil : Columns Unit where
  names := []
  toVals _ := []
  ofVals
    | [] => some ()
    | _ :: _ => none
  ofVals_toVals _ := rfl
  ofVals_exact := by
    intro vs r h
    cases vs with
    | nil => rfl
    | cons _ _ => nomatch h

def Columns.cons {α ρ : Type} (n : String) (I : Image α) (R : Columns ρ) : Columns (α × ρ) where
  names := n :: R.names
  toVals x := I.toVal x.1 :: R.toVals x.2
  ofVals
    | v :: vs => (I.ofVal v).bind fun a => (R.ofVals vs).map fun r => (a, r)
    | [] => none
  ofVals_toVals x := by
    show (I.ofVal (I.toVal x.1)).bind (fun a => (R.ofVals (R.toVals x.2)).map fun r => (a, r)) =
      some x
    rw [I.ofVal_toVal, R.ofVals_toVals]
    rfl
  ofVals_exact := by
    intro vs x h
    cases vs with
    | nil => nomatch h
    | cons v vs =>
      change (I.ofVal v).bind (fun a => (R.ofVals vs).map fun r => (a, r)) = some x at h
      cases hv : I.ofVal v with
      | none => rw [hv] at h; nomatch h
      | some a =>
        cases hr : R.ofVals vs with
        | none => rw [hv, hr] at h; nomatch h
        | some r =>
          rw [hv, hr] at h
          cases h
          show v :: vs = I.toVal a :: R.toVals r
          rw [I.ofVal_exact hv, R.ofVals_exact hr]

/-- **A record's image**: the machine's record frame, names first, values second. -/
def Image.record {ρ : Type} (R : Columns ρ) : Image ρ where
  toVal r := .ctor 0 [.list (R.names.map .str), .list (R.toVals r)]
  ofVal v := match v with
    | .ctor 0 [.list ns, .list vs] => if ns = R.names.map .str then R.ofVals vs else none
    | _ => none
  ofVal_toVal r := by
    show (if R.names.map Val.str = R.names.map Val.str then R.ofVals (R.toVals r) else none) = some r
    rw [if_pos rfl, R.ofVals_toVals]
  ofVal_exact := by
    intro v r h
    split at h
    · rename_i ns vs
      split at h
      · rename_i hns
        rw [hns, R.ofVals_exact h]
      · nomatch h
    · nomatch h

def emptyImage : Image Empty where
  toVal e := e.elim
  ofVal _ := none
  ofVal_toVal e := e.elim
  ofVal_exact := by intro _ _ h; nomatch h

/-! ## The carrier fold -/

/-- A carrier with its exact embedding. -/
abbrev M := Σ α : Type, Image α

def refused : M := ⟨Empty, emptyImage⟩

/-- A record's fields: one column each, in the schema's order. An optional field has no
carrier yet. -/
def columnsOf : List (String × Bool × M) → Σ ρ : Type, Columns ρ
  | [] => ⟨Unit, Columns.nil⟩
  | (n, false, m) :: rest => ⟨m.1 × (columnsOf rest).1, Columns.cons n m.2 (columnsOf rest).2⟩
  | (n, true, _) :: rest => ⟨Empty × (columnsOf rest).1, Columns.cons n emptyImage (columnsOf rest).2⟩

/-- **The carrier algebra**: each supported constructor's carrier and image. -/
def modelAlg : TyAlgebra (fun _ => M) where
  ty_never := refused
  ty_unit := ⟨Unit, Store.Image.unit⟩
  ty_nat := ⟨Nat, Store.Image.nat⟩
  ty_int := refused
  ty_string := ⟨String, Store.Image.string⟩
  ty_bool := ⟨Bool, Store.Image.bool⟩
  ty_handle _ := refused
  ty_option m := ⟨Option m.1, Store.Image.option m.2⟩
  ty_list m := ⟨List m.1, Store.Image.list m.2⟩
  ty_prod a b := ⟨a.1 × b.1, Store.Image.tuple2 a.2 b.2⟩
  ty_except _ _ := refused
  ty_exitOf _ _ := refused
  ty_causeOf _ := refused
  ty_fiberOf _ _ := refused
  ty_union _ _ := refused
  ty_lit _ := refused
  ty_refOf _ := refused
  ty_deferredOf _ _ := refused
  ty_var _ := refused
  ty_unknown := refused
  ty_record fs := ⟨(columnsOf fs).1, Image.record (columnsOf fs).2⟩
  ty_map _ _ := refused
  ty_tuple _ := refused
  ty_app _ _ := refused
  ty_null := refused
  ty_undefined := refused
  ty_number := refused
  ty_bytes := refused

def Carrier (t : Ty) : Type := (cata_ty modelAlg t).1
def image (t : Ty) : Image (Carrier t) := (cata_ty modelAlg t).2

/-- The refusal fold: the first constructor that has no carrier yet, by name. -/
def refusalAlg : TyAlgebra (fun _ => Option String) where
  ty_never := some "never"
  ty_unit := none
  ty_nat := none
  ty_int := some "int"
  ty_string := none
  ty_bool := none
  ty_handle _ := some "handle: an identity needs its table"
  ty_option m := m
  ty_list m := m
  ty_prod a b := a.or b
  ty_except _ _ := some "except"
  ty_exitOf _ _ := some "exitOf"
  ty_causeOf _ := some "causeOf"
  ty_fiberOf _ _ := some "fiberOf: an identity needs its table"
  ty_union _ _ := some "union"
  ty_lit _ := some "lit"
  ty_refOf _ := some "refOf: an identity needs its table"
  ty_deferredOf _ _ := some "deferredOf: an identity needs its table"
  ty_var _ := some "var"
  ty_unknown := some "unknown"
  ty_record fs := fs.foldr (fun (n, opt, m) acc =>
    if opt then some s!"optional field {n}" else m.or acc) none
  ty_map _ _ := some "map"
  ty_tuple _ := some "tuple"
  ty_app _ _ := some "app"
  ty_null := some "null"
  ty_undefined := some "undefined"
  ty_number := some "number"
  ty_bytes := some "bytes"

def refusal (t : Ty) : Option String := cata_ty refusalAlg t

/-! ## Lean types tied to `Ty` -/

/-- A Lean type with its `Ty` and an equivalence to that `Ty`'s carrier. -/
class Modeled (α : Type) where
  ty : Ty
  toC : α → Carrier ty
  ofC : Carrier ty → α
  to_of : ∀ c, toC (ofC c) = c
  of_to : ∀ a, ofC (toC a) = a

/-- The exact embedding of a modeled type: the carrier's, across the equivalence. -/
def Modeled.image (α : Type) [m : Modeled α] : Image α :=
  Store.Image.equiv (TyModel.image m.ty) m.ofC m.toC m.of_to m.to_of

instance : Modeled Bool := ⟨.bool, id, id, fun _ => rfl, fun _ => rfl⟩
instance : Modeled Nat := ⟨.nat, id, id, fun _ => rfl, fun _ => rfl⟩
instance : Modeled String := ⟨.string, id, id, fun _ => rfl, fun _ => rfl⟩

theorem list_inv {α β : Type} (f : β → α) (g : α → β) (h : ∀ a, f (g a) = a) :
    ∀ xs : List α, (xs.map g).map f = xs
  | [] => rfl
  | x :: rest => by
    show f (g x) :: (rest.map g).map f = x :: rest
    rw [h, list_inv f g h rest]

theorem option_inv {α β : Type} (f : β → α) (g : α → β) (h : ∀ a, f (g a) = a) :
    ∀ o : Option α, (o.map g).map f = o
  | none => rfl
  | some x => by
    show some (f (g x)) = some x
    rw [h]

instance {α : Type} [m : Modeled α] : Modeled (List α) where
  ty := .list m.ty
  toC xs := xs.map m.toC
  ofC cs := List.map m.ofC cs
  to_of := list_inv m.toC m.ofC m.to_of
  of_to := list_inv m.ofC m.toC m.of_to

instance {α : Type} [m : Modeled α] : Modeled (Option α) where
  ty := .option m.ty
  toC o := o.map m.toC
  ofC c := Option.map m.ofC c
  to_of := option_inv m.toC m.ofC m.to_of
  of_to := option_inv m.ofC m.toC m.of_to

/-! ## The deriving command -/

/-- Field spellings in canonical order: ascending by their bytes. -/
def canonicalOrder (names : List String) : List String :=
  (Effect4.Field.canonBy Effect4.Field.bytesKey (names.map fun n => (n, ()))).map Prod.fst

syntax "derive_modeled " ident ("(" ident " := " str ")")* : command

elab_rules : command
  | `(derive_modeled $s:ident $[($rf:ident := $rn:str)]*) => do
    let sName ← liftCoreM (realizeGlobalConstNoOverload s)
    let env ← getEnv
    unless isStructure env sName do throwError "{sName} is not a structure"
    let fields := getStructureFields env sName
    let renames : List (Name × String) :=
      (rf.zip rn).toList.map fun (f, n) => (f.getId, n.getString)
    let spelling (f : Name) : String := (renames.lookup f).getD f.toString
    let ctor := getStructureCtor env sName
    let fieldTys ← liftTermElabM <| forallTelescope ctor.type fun xs _ => do
      xs.toList.mapM fun x => do PrettyPrinter.delab (← inferType x)
    let entries := (fields.toList.zip fieldTys).map fun (f, t) => (f, spelling f, t)
    let order := canonicalOrder (entries.map (·.2.1))
    let sorted := order.filterMap fun sp => entries.find? (·.2.1 == sp)
    -- The `Ty`, in canonical order.
    let tyItems ← sorted.mapM fun (_, sp, t) =>
      `(($(quote sp), false, (Modeled.ty (α := $t))))
    -- The carrier projections: `c.1`, `c.2.1`, `c.2.2.1`, ...
    let cId := mkIdent `c
    let proj (k : Nat) : MacroM (TSyntax `term) := do
      let mut acc : TSyntax `term ← `($cId)
      for _ in [0:k] do acc ← `(($acc).2)
      `(($acc).1)
    let toItems ← sorted.mapM fun (f, _, _) =>
      `(Modeled.toC ($(mkIdent (sName ++ f)) s))
    let tuple ← toItems.foldrM (fun x acc => `(($x, $acc))) (← `(()))
    let ofFields ← liftMacroM <| (entries.mapM fun (f, sp, _) => do
      let k := (sorted.findIdx? (·.2.1 == sp)).getD 0
      let p ← proj k
      `(Lean.Parser.Term.structInstField| $(mkIdent f):ident := Modeled.ofC $p))
    let vars : List (TSyntax `term) :=
      (List.range sorted.length).map fun i => ⟨(mkIdent (.mkSimple s!"x{i}")).raw⟩
    let pat ← vars.foldrM (fun x acc => `(($x, $acc))) (← `(()))
    let inv ← vars.foldrM (fun x acc => `(Prod.ext (Modeled.to_of $x) $acc)) (← `(rfl))
    let tyId := mkIdent (`_root_ ++ sName ++ `modeledTy)
    let toId := mkIdent (`_root_ ++ sName ++ `modeledToC)
    let ofId := mkIdent (`_root_ ++ sName ++ `modeledOfC)
    let toOfId := mkIdent (`_root_ ++ sName ++ `modeled_to_of)
    let ofToId := mkIdent (`_root_ ++ sName ++ `modeled_of_to)
    elabCommand (← `(def $tyId : Ty := .record [$(tyItems.toArray),*]))
    elabCommand (← `(def $toId (s : $s) : Carrier $tyId := $tuple))
    let fieldsArr := ofFields.toArray
    elabCommand (← `(def $ofId ($cId : Carrier $tyId) : $s := { $fieldsArr:structInstField,* }))
    elabCommand (← `(theorem $toOfId : ∀ $cId : Carrier $tyId, $toId ($ofId $cId) = $cId :=
      fun $pat => $inv))
    elabCommand (← `(theorem $ofToId (s : $s) : $ofId ($toId s) = s := by
      cases s
      simp only [$toId:ident, $ofId:ident, Modeled.of_to]))
    elabCommand (← `(instance : Modeled $s := ⟨$tyId, $toId, $ofId, $toOfId, $ofToId⟩))

/-! ## Latch's cell, declared once -/

structure Waiter where
  id : Nat
  hint : Nat
  deriving DecidableEq, Repr

structure LatchCell where
  waiters : List Waiter
  isOpen : Bool
  deriving DecidableEq, Repr

derive_modeled Waiter
derive_modeled LatchCell (isOpen := "open")

def cell : LatchCell := ⟨[⟨4, 5⟩], false⟩

end TyModel

open TyModel

-- The derived `Ty`: fields in canonical order, under their spellings.
#eval toString (repr (Modeled.ty (α := LatchCell)))
-- No constructor of the cell's `Ty` lacks a carrier.
#guard refusal (Modeled.ty (α := LatchCell)) == none
-- An identity type is refused by name: the waiters' real identities need their table.
#guard refusal (.record [("id", false, .deferredOf .unit .never)]) ==
  some "deferredOf: an identity needs its table"
-- The value of the cell is the machine's record frame, in canonical order.
#guard (Modeled.image LatchCell).toVal cell ==
  .ctor 0 [.list [.str "open", .str "waiters"],
    .list [.bool false, .list [.ctor 0 [.list [.str "hint", .str "id"], .list [.nat 5, .nat 4]]]]]
-- It reads back exactly.
#guard (Modeled.image LatchCell).ofVal ((Modeled.image LatchCell).toVal cell) == some cell
-- It inhabits the derived type, by the program's own membership check.
#guard Val.hasTy ((Modeled.image LatchCell).toVal cell) (Modeled.ty (α := LatchCell)) [] == true
-- The TypeScript type of the cell.
#eval (Codegen.Types.ofTy (Modeled.ty (α := LatchCell))).map (TypeScript.Render.type TypeScript.house0)
-- The Effect Schema representation of the cell, printed.
#eval TypeScript.Render.expr TypeScript.house0 0
  (Codegen.Schema.representation (Ty.schema (Modeled.ty (α := LatchCell))))
-- JSON and back: Lean value, value tree, JSON, value tree, Lean value.
#guard (Effect4.Schema.encode (Modeled.ty (α := LatchCell))
  ((Modeled.image LatchCell).toVal cell)).isSome
#guard ((Effect4.Schema.encode (Modeled.ty (α := LatchCell)) ((Modeled.image LatchCell).toVal cell)).bind
    (Effect4.Schema.decode (Modeled.ty (α := LatchCell)))).bind (Modeled.image LatchCell).ofVal ==
  some cell

#print axioms TyModel.LatchCell.modeled_to_of
#print axioms TyModel.LatchCell.modeled_of_to
#print axioms TyModel.Image.record
