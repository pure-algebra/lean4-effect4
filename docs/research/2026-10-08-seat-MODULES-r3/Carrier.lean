import Effect4
import Effect4.Schema.Codec
import Effect4.Laws.Schema.Codec
import Effect4.Laws.Program.TypeAlgebra

/-! Probe MODS-12, after Codex's second review (`docs/research/2026-10-08-modules-r2-review.md`,
findings R2-F1 and R2-F5).

- **One checked domain.** The refusal fold also refuses a record whose names are not in canonical
  order, and an optional field. A `Ty` is in the domain when the fold answers `none`.
- **Membership, once.** `member`: on the checked domain, every carrier value's encoding inhabits
  the type, for every allocation table. One theorem, by structural recursion on `Ty`.
- **A class that cannot be cheated.** `Modeled` carries a proof that its `Ty` is in the domain;
  the carrier and the image are the fold's, never the instance's. Its membership is `member`.
- **Deriving with validation.** Rename sources must exist, a rename source appears once, the
  spellings are distinct, the structure has no parameters, and each field type has an instance:
  each failure is a refusal located at its syntax, before any declaration is written.

The carrier fold and the record image are MODS-11's, unchanged. -/

set_option autoImplicit false

open Lean Elab Command Term Meta
open Effect4 Effect4.Program Effect4.Store

namespace Carrier3

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

/-! ## The checked domain -/

/-- Field names strictly ascending by their bytes. -/
def Ascending (names : List String) : Prop :=
  names.Pairwise fun a b => Field.ltKey (Field.bytesKey a) (Field.bytesKey b) = true

instance (names : List String) : Decidable (Ascending names) := by
  unfold Ascending; exact inferInstance

/-- A record's fields: refused at an optional field, or at a field's own refusal. -/
def fieldsRefusal : List (String × Bool × Option String) → Option String
  | [] => none
  | (n, true, _) :: _ => some s!"optional field {n}"
  | (_, false, m) :: rest => m.or (fieldsRefusal rest)

/-- The refusal fold: the first reason a `Ty` is outside the checked domain, by name. -/
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
  ty_record fs := if Ascending (fs.map (·.1)) then fieldsRefusal fs
    else some "record fields out of canonical order"
  ty_map _ _ := some "map"
  ty_tuple _ := some "tuple"
  ty_app _ _ := some "app"
  ty_null := some "null"
  ty_undefined := some "undefined"
  ty_number := some "number"
  ty_bytes := some "bytes"

def refusal (t : Ty) : Option String := cata_ty refusalAlg t

/-! ## Membership, once for the checked domain -/

theorem or_none {a b : Option String} (h : a.or b = none) : a = none ∧ b = none := by
  cases a with
  | none => exact ⟨rfl, h⟩
  | some _ => nomatch h

theorem checkers_names (alloc : List String) : ∀ fs : List (String × Bool × Ty),
    (Val.fieldCheckers fs alloc).map (·.1) = fs.map (·.1)
  | [] => rfl
  | (n, o, t) :: rest => by
    show n :: (Val.fieldCheckers rest alloc).map (·.1) = n :: rest.map (·.1)
    rw [checkers_names alloc rest]

theorem columns_names : ∀ fs : List (String × Bool × Ty),
    (columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg fs)).2.names = fs.map (·.1)
  | [] => rfl
  | (n, false, t) :: rest => by
    show n :: (columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg rest)).2.names =
      n :: rest.map (·.1)
    rw [columns_names rest]
  | (n, true, t) :: rest => by
    show n :: (columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg rest)).2.names =
      n :: rest.map (·.1)
    rw [columns_names rest]

mutual
/-- **Membership**: on the checked domain, every carrier value's encoding inhabits its type. -/
theorem member : (t : Ty) → refusal t = none → ∀ (x : Carrier t) (alloc : List String),
    Val.hasTy ((image t).toVal x) t alloc = true
  | .unit, _, _, _ => rfl
  | .nat, _, _, _ => rfl
  | .string, _, _, _ => rfl
  | .bool, _, _, _ => rfl
  | .option inner, h, x, alloc => by
    cases x with
    | none => rfl
    | some a => exact member inner h a alloc
  | .list inner, h, x, alloc => by
    show (x.map (image inner).toVal).all (fun v => Val.hasTy v inner alloc) = true
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact member inner h a alloc
  | .prod a b, h, x, alloc => by
    have hab := or_none h
    show (Val.hasTy ((image a).toVal x.1) a alloc && Val.hasTy ((image b).toVal x.2) b alloc) = true
    rw [member a hab.1 x.1 alloc, member b hab.2 x.2 alloc]
    rfl
  | .record fs, h, x, alloc => by
    change (if Ascending ((cata_pos_list_prod_string_prod_bool_ty refusalAlg fs).map (·.1)) then
      fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
      else some "record fields out of canonical order") = none at h
    split at h
    · rename_i hasc
      have hnames : (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs).map (·.1) =
          fs.map (·.1) := names_map_refusal fs
      rw [hnames] at hasc
      have hcanon : Ty.canon (Val.fieldCheckers fs alloc) = Val.fieldCheckers fs alloc := by
        apply Field.canonBy_of_ascending
        unfold Field.Ascending
        unfold Ascending at hasc
        rw [← checkers_names alloc fs] at hasc
        rw [List.pairwise_map] at hasc
        exact hasc
      show (match Program.recordParts? (.ctor 0 [.list ((columnsOf
          (cata_pos_list_prod_string_prod_bool_ty modelAlg fs)).2.names.map .str),
          .list ((columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg fs)).2.toVals x)]) with
        | some (ns, xs) => namedHasTy (Ty.canon (Val.fieldCheckers fs alloc)) ns xs
        | none => false) = true
      simp only [Program.recordParts?]
      rw [hcanon, columns_names fs]
      exact member_fields fs h x alloc
    · nomatch h
  | .never, h, _, _ => nomatch h
  | .int, h, _, _ => nomatch h
  | .handle _, h, _, _ => nomatch h
  | .except _ _, h, _, _ => nomatch h
  | .exitOf _ _, h, _, _ => nomatch h
  | .causeOf _, h, _, _ => nomatch h
  | .fiberOf _ _, h, _, _ => nomatch h
  | .union _ _, h, _, _ => nomatch h
  | .lit _, h, _, _ => nomatch h
  | .refOf _, h, _, _ => nomatch h
  | .deferredOf _ _, h, _, _ => nomatch h
  | .var _, h, _, _ => nomatch h
  | .unknown, h, _, _ => nomatch h
  | .map _ _, h, _, _ => nomatch h
  | .tuple _, h, _, _ => nomatch h
  | .app _ _, h, _, _ => nomatch h
  | .null, h, _, _ => nomatch h
  | .undefined, h, _, _ => nomatch h
  | .number, h, _, _ => nomatch h
  | .bytes, h, _, _ => nomatch h

/-- The record arm, field by field: each value passes its field's check, in order. -/
theorem member_fields : (fs : List (String × Bool × Ty)) →
    fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs) = none →
    ∀ (x : (columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg fs)).1) (alloc : List String),
      namedHasTy (Val.fieldCheckers fs alloc) ((fs.map (·.1)).map .str)
        ((columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg fs)).2.toVals x) = true
  | [], _, _, _ => rfl
  | (n, false, t) :: rest, h, x, alloc => by
    have ht := or_none h
    show (if n = n then Val.hasTy ((image t).toVal x.1) t alloc &&
        namedHasTy (Val.fieldCheckers rest alloc) ((rest.map (·.1)).map .str)
          ((columnsOf (cata_pos_list_prod_string_prod_bool_ty modelAlg rest)).2.toVals x.2)
      else false && _) = true
    rw [if_pos rfl, member t ht.1 x.1 alloc, member_fields rest ht.2 x.2 alloc]
    rfl
  | (_, true, _) :: _, h, _, _ => nomatch h

/-- The refusal fold keeps a record's names. -/
theorem names_map_refusal : (fs : List (String × Bool × Ty)) →
    (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs).map (·.1) = fs.map (·.1)
  | [] => rfl
  | (n, o, t) :: rest => by
    show n :: (cata_pos_list_prod_string_prod_bool_ty refusalAlg rest).map (·.1) =
      n :: rest.map (·.1)
    rw [names_map_refusal rest]
end

/-! ## A class that cannot be cheated -/

/-- A Lean type with a `Ty` in the checked domain and an equivalence to the fold's carrier. -/
class Modeled (α : Type) where
  ty : Ty
  checked : refusal ty = none
  toC : α → Carrier ty
  ofC : Carrier ty → α
  to_of : ∀ c, toC (ofC c) = c
  of_to : ∀ a, ofC (toC a) = a

def Modeled.image (α : Type) [m : Modeled α] : Image α :=
  Store.Image.equiv (Carrier3.image m.ty) m.ofC m.toC m.of_to m.to_of

/-- **Every modeled value inhabits its type**: `member` across the equivalence, no instance law. -/
theorem Modeled.member (α : Type) [m : Modeled α] (a : α) (alloc : List String) :
    Val.hasTy ((Modeled.image α).toVal a) m.ty alloc = true :=
  Carrier3.member m.ty m.checked (m.toC a) alloc

instance : Modeled Bool := ⟨.bool, rfl, id, id, fun _ => rfl, fun _ => rfl⟩
instance : Modeled Nat := ⟨.nat, rfl, id, id, fun _ => rfl, fun _ => rfl⟩
instance : Modeled String := ⟨.string, rfl, id, id, fun _ => rfl, fun _ => rfl⟩

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
  checked := m.checked
  toC xs := xs.map m.toC
  ofC cs := List.map m.ofC cs
  to_of := list_inv m.toC m.ofC m.to_of
  of_to := list_inv m.ofC m.toC m.of_to

instance {α : Type} [m : Modeled α] : Modeled (Option α) where
  ty := .option m.ty
  checked := m.checked
  toC o := o.map m.toC
  ofC c := Option.map m.ofC c
  to_of := option_inv m.toC m.ofC m.to_of
  of_to := option_inv m.ofC m.toC m.of_to

/-! ## Deriving, with validation -/

def canonicalOrder (names : List String) : List String :=
  (Effect4.Field.canonBy Effect4.Field.bytesKey (names.map fun n => (n, ()))).map Prod.fst

syntax "derive_modeled " ident ("(" ident " := " str ")")* : command

elab_rules : command
  | `(derive_modeled $s:ident $[($rf:ident := $rn:str)]*) => do
    let sName ← liftCoreM (realizeGlobalConstNoOverload s)
    let env ← getEnv
    unless isStructure env sName do
      throwErrorAt s "derive_modeled: {sName} is not a structure"
    let ctor := getStructureCtor env sName
    unless ctor.numParams == 0 do
      throwErrorAt s "derive_modeled: {sName} has parameters; the first profile is monomorphic"
    let fields := (getStructureFields env sName).toList
    -- Each rename names an existing field, once.
    let mut seen : List Name := []
    for f in rf do
      unless fields.contains f.getId do
        throwErrorAt f "derive_modeled: {sName} has no field {f.getId}"
      if seen.contains f.getId then
        throwErrorAt f "derive_modeled: field {f.getId} is renamed twice"
      seen := f.getId :: seen
    let renames : List (Name × String) :=
      (rf.zip rn).toList.map fun (f, n) => (f.getId, n.getString)
    let spelling (f : Name) : String := (renames.lookup f).getD f.toString
    -- The spellings are distinct.
    let spellings := fields.map spelling
    for f in fields do
      if (spellings.filter (· == spelling f)).length > 1 then
        throwErrorAt s "derive_modeled: two fields of {sName} are spelled {spelling f}"
    -- Each field is non-dependent, and its type has an instance.
    let fieldTys ← liftTermElabM <| forallTelescope ctor.type fun xs _ => do
      unless xs.size == fields.length do
        throwError "derive_modeled: {sName}'s constructor does not match its fields"
      xs.toList.mapM fun x => do
        let t ← inferType x
        if t.hasAnyFVar (fun v => xs.any (·.fvarId! == v)) then
          throwError "derive_modeled: field type {t} depends on another field"
        let inst ← mkAppM ``Modeled #[t]
        if (← trySynthInstance inst) matches .some _ then pure ()
        else throwError "derive_modeled: field type {t} has no Modeled instance"
        PrettyPrinter.delab t
    let entries := (fields.zip fieldTys).map fun (f, t) => (f, spelling f, t)
    let order := canonicalOrder (entries.map (·.2.1))
    let sorted := order.filterMap fun sp => entries.find? (·.2.1 == sp)
    let tyItems ← sorted.mapM fun (_, sp, t) =>
      `(($(quote sp), false, (Modeled.ty (α := $t))))
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
    let checkedId := mkIdent (`_root_ ++ sName ++ `modeled_checked)
    let toId := mkIdent (`_root_ ++ sName ++ `modeledToC)
    let ofId := mkIdent (`_root_ ++ sName ++ `modeledOfC)
    let toOfId := mkIdent (`_root_ ++ sName ++ `modeled_to_of)
    let ofToId := mkIdent (`_root_ ++ sName ++ `modeled_of_to)
    let fieldsArr := ofFields.toArray
    elabCommand (← `(def $tyId : Ty := .record [$(tyItems.toArray),*]))
    elabCommand (← `(theorem $checkedId : refusal $tyId = none := by decide))
    elabCommand (← `(def $toId (s : $s) : Carrier $tyId := $tuple))
    elabCommand (← `(def $ofId ($cId : Carrier $tyId) : $s := { $fieldsArr:structInstField,* }))
    elabCommand (← `(theorem $toOfId : ∀ $cId : Carrier $tyId, $toId ($ofId $cId) = $cId :=
      fun $pat => $inv))
    elabCommand (← `(theorem $ofToId (s : $s) : $ofId ($toId s) = s := by
      cases s
      simp only [$toId:ident, $ofId:ident, Modeled.of_to]))
    elabCommand (← `(instance : Modeled $s :=
      ⟨$tyId, $checkedId, $toId, $ofId, $toOfId, $ofToId⟩))

end Carrier3

/-! ## The JSON codec: its own obligation, with its premise -/

namespace Carrier3

/-- **The codec round trip of a modeled value**, at the normal form of its type. Membership comes
from `Modeled.member`; codec admission is value-specific (`Ty.isCodecValue`) and stays a premise:
a number above 2^53 inhabits `nat` but has no exact JSON image. -/
theorem Modeled.codec_roundtrip (α : Type) [m : Modeled α] (a : α)
    (admitted : Ty.isCodecValue (CTy.ofRaw m.ty).toRaw ((Modeled.image α).toVal a) = true) :
    ((Effect4.Schema.encode (CTy.ofRaw m.ty).toRaw ((Modeled.image α).toVal a)).bind
        (Effect4.Schema.decode (CTy.ofRaw m.ty).toRaw)).bind (Modeled.image α).ofVal = some a := by
  have hmem : Val.hasTy ((Modeled.image α).toVal a) (CTy.ofRaw m.ty).toRaw = true := by
    show Val.hasTy _ m.ty.normalize [] = true
    rw [hasTy_normalize]
    exact Modeled.member α a []
  rw [Effect4.Schema.decode_encode hmem admitted]
  exact (Modeled.image α).ofVal_toVal a

end Carrier3

/-! ## An ordinary nested record, derived -/

namespace Carrier3.Example

structure Waiter where
  id : Nat
  hint : Nat
  deriving DecidableEq, Repr

structure LatchCell where
  waiters : List Waiter
  isOpen : Bool
  label : Option String
  deriving DecidableEq, Repr

derive_modeled Waiter
derive_modeled LatchCell (isOpen := "open")

def cell : LatchCell := ⟨[⟨4, 5⟩], false, some "gate"⟩

/-- Membership of every cell value, at every allocation table: no proof of its own. -/
example (c : LatchCell) (alloc : List String) :
    Val.hasTy ((Modeled.image LatchCell).toVal c) (Modeled.ty (α := LatchCell)) alloc = true :=
  Modeled.member LatchCell c alloc

end Carrier3.Example

open Carrier3 Carrier3.Example

#guard Modeled.ty (α := LatchCell) == .record [("label", false, .option .string),
  ("open", false, .bool),
  ("waiters", false, .list (.record [("hint", false, .nat), ("id", false, .nat)]))]
#guard (Modeled.image LatchCell).ofVal ((Modeled.image LatchCell).toVal cell) == some cell
-- The codec premise is decidable on a value: true for this cell, false for a number above 2^53.
#guard Ty.isCodecValue (CTy.ofRaw (Modeled.ty (α := LatchCell))).toRaw
  ((Modeled.image LatchCell).toVal cell)
#guard !Ty.isCodecValue (CTy.ofRaw (Modeled.ty (α := Nat))).toRaw ((Modeled.image Nat).toVal (2^53 + 1))
#guard (Modeled.image LatchCell).toVal cell ==
  .ctor 0 [.list [.str "label", .str "open", .str "waiters"],
    .list [.some (.str "gate"), .bool false,
      .list [.ctor 0 [.list [.str "hint", .str "id"], .list [.nat 5, .nat 4]]]]]

/-! ## Red controls: each malformed input of the review is refused, for its reason -/

namespace Carrier3.Controls

structure Unsorted where
  z : Bool
  a : Bool

-- A hand instance whose record names are out of canonical order: its check fails.
/--
error: Tactic `decide` proved that the proposition
  refusal (Ty.record [("z", false, Ty.bool), ("a", false, Ty.bool)]) = none
is false
-/
#guard_msgs in
instance : Modeled Unsorted where
  ty := .record [("z", false, .bool), ("a", false, .bool)]
  checked := by decide
  toC s := (s.z, (s.a, ()))
  ofC c := ⟨c.1, c.2.1⟩
  to_of := fun (_, (_, ())) => rfl
  of_to := fun ⟨_, _⟩ => rfl

-- A hand instance at an identity type: its check fails.
/--
error: Tactic `decide` proved that the proposition
  refusal (Ty.handle "Unimplemented.Identity") = none
is false
-/
#guard_msgs in
instance : Modeled Empty where
  ty := .handle "Unimplemented.Identity"
  checked := by decide
  toC x := x.elim
  ofC x := x
  to_of := fun x => x.elim
  of_to := fun x => x.elim

structure Renamed where
  original : Bool

-- A rename of a field that does not exist.
/-- error: derive_modeled: Carrier3.Controls.Renamed has no field misspelled -/
#guard_msgs in
derive_modeled Renamed (misspelled := "changed")

structure TwoFlags where
  left : Bool
  right : Bool

-- Two fields under one spelling.
/-- error: derive_modeled: two fields of Carrier3.Controls.TwoFlags are spelled flag -/
#guard_msgs in
derive_modeled TwoFlags (left := "flag") (right := "flag")

-- One field renamed twice.
/-- error: derive_modeled: field left is renamed twice -/
#guard_msgs in
derive_modeled TwoFlags (left := "a") (left := "b")

structure Boxed (α : Type) where
  value : α

-- A structure with parameters.
/--
error: derive_modeled: Carrier3.Controls.Boxed has parameters; the first profile is monomorphic
-/
#guard_msgs in
derive_modeled Boxed

structure Holder where
  stamp : Int

-- A field type with no instance.
/-- error: derive_modeled: field type Int has no Modeled instance -/
#guard_msgs in
derive_modeled Holder

end Carrier3.Controls

#print axioms Carrier3.member
#print axioms Carrier3.Modeled.codec_roundtrip
#print axioms Carrier3.Modeled.member
#print axioms Carrier3.Example.LatchCell.modeled_to_of
