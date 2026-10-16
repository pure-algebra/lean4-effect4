module

public import Effect4.Program.Fold
public import Effect4.Program.TyNormal
public import Effect4.Program.TyExpand
public import Effect4.Store.Carrier.Image.Containers
public import Effect4.Store.Carrier.Image.Record

/-!
# Schema.Modeled — Lean types tied to `Ty` by one fold

The schema plane's carrier fold (`Model.alg`) gives each supported `Ty` its Lean carrier and its
exact embedding into `Store.Val` together. It is a `TyAlgebra`, so it reduces on a concrete type:
`Model.Carrier (.list .nat)` is `List Nat`. A record type's carrier is the product of its fields'
carriers, written into the record frame (`Store.Image.record`).

The fold takes an **identity context** (`Model.Leaves`): the carrier of each identity type, the
handle, the reference, the `Deferred` and the fiber. `Model.alg` is the fold at the context that
refuses every identity (`Leaves.refused`). The context that carries an identity as its own value
(`Leaves.opaque`) lets a step read and write a record that holds identities, Semaphore's cell
among them (`src/Effect4/Step.lean`).

The **checked domain** is the set of types the refusal fold (`Model.refusalAlg`) answers `none`
at. An integer is its `nat` or `negInt` frame (`Image.int`), a literal the unit carrier of its one
string (`Image.lit`), and a union the values of a sum that exactly one side reads
(`Image.union`): for a union of records with distinct `_tag` literals that is every value of the
sum, so `deriving Modeled` on an inductive writes one (`Schema.Modeled.Derive`). It refuses an
identity type, since an identity needs its role's table; an optional field;
a record whose names are not strictly ascending by their bytes (`Field.Ascending`); and every
constructor that has no carrier yet. On the checked domain every encoded value inhabits its type
(`Effect4.Schema.Model.member`, `src/Effect4/Laws/Schema/Modeled.lean`).
Tuple carriers serve stored step results. The checked domain still refuses tuple types.

`Modeled α` ties a Lean type to a checked `Ty` by an equivalence with that type's carrier. An
instance proves its type checked, and its image is the fold's, carried across the equivalence,
so an instance owes no membership proof and cannot supply a wrong one. `deriving Modeled` and
`derive_modeled` write the instance of a structure (`Effect4.Schema.Modeled.Derive`).

The decisions row is 330 (the MODULES design, slice L1).
-/

@[expose] public section

namespace Effect4.Schema
open Effect4.Program Effect4.Store

namespace Model

/-- A carrier with its exact embedding. -/
abbrev M := Σ α : Type, Image α

/-- The carrier of a constructor outside the checked domain: empty. -/
def refused : M := ⟨Empty, Image.empty⟩

/-- **An identity context**: the carrier of each identity type, by its role, and the carrier of
a type variable. An identity's carrier does not depend on what the handle holds. A type variable
stands for a module's type parameter: a step's term never reads it. -/
structure Leaves where
  handle : String → M
  ref : M
  deferred : M
  fiber : M
  var : M

/-- The context of the checked domain: every identity is refused, since it needs its table. -/
def Leaves.refused : Leaves :=
  ⟨fun _ => Model.refused, Model.refused, Model.refused, Model.refused, Model.refused⟩

/-- The context that carries an identity, and a value of a type variable, as its own value, with
the carrier's own image (`Image.ident`). A step reads and writes such a field as it is, and
never inspects it. -/
def Leaves.opaque : Leaves :=
  ⟨fun _ => ⟨Val, Image.ident⟩, ⟨Val, Image.ident⟩, ⟨Val, Image.ident⟩, ⟨Val, Image.ident⟩,
    ⟨Val, Image.ident⟩⟩

/-- A field's carrier: its type's, or empty for an optional field, which has no carrier yet. -/
def fieldCarrier : Bool → M → M
  | false, m => m
  | true, _ => refused

/-- A record's fields, one column each, in the type's order. The shape is one product per
field, whether the field is optional or not. -/
def columnsOf : List (String × Bool × M) → Σ ρ : Type, Columns ρ
  | [] => ⟨Unit, Columns.nil⟩
  | (n, o, m) :: rest =>
    ⟨(fieldCarrier o m).1 × (columnsOf rest).1, Columns.cons n (fieldCarrier o m).2 (columnsOf rest).2⟩

/-- Tuple items share the exact columns, with names unused by their flat image.
A helper of step-language-sound, consumed by the tuple3 step carrier. -/
def tupleColumnsOf : List M → Σ ρ : Type, Columns ρ
  | [] => ⟨Unit, Columns.nil⟩
  | m :: rest => ⟨m.1 × (tupleColumnsOf rest).1,
      Columns.cons "" m.2 (tupleColumnsOf rest).2⟩

/-- **The carrier algebra** at an identity context: each supported constructor's carrier and its
image. -/
def algAt (L : Leaves) : TyAlgebra (fun _ => M) where
  ty_never := refused
  ty_unit := ⟨Unit, Image.unit⟩
  ty_nat := ⟨Nat, Image.nat⟩
  ty_int := ⟨Int, Image.int⟩
  ty_string := ⟨String, Image.string⟩
  ty_bool := ⟨Bool, Image.bool⟩
  ty_handle n := L.handle n
  ty_option m := ⟨Option m.1, Image.option m.2⟩
  ty_list m := ⟨List m.1, Image.list m.2⟩
  ty_prod a b := ⟨a.1 × b.1, Image.tuple2 a.2 b.2⟩
  ty_except _ _ := refused
  ty_exitOf _ _ := refused
  ty_causeOf _ := refused
  ty_fiberOf _ _ := L.fiber
  ty_union a b := ⟨{s : Sum a.1 b.1 // Image.unambiguous a.2 b.2 s = true}, Image.union a.2 b.2⟩
  ty_lit s := ⟨Unit, Image.lit s⟩
  ty_refOf _ := L.ref
  ty_deferredOf _ _ := L.deferred
  ty_var _ := L.var
  ty_unknown := refused
  ty_record fs := ⟨(columnsOf fs).1, Image.record (columnsOf fs).2⟩
  ty_map _ _ := refused
  ty_tuple ms := ⟨(tupleColumnsOf ms).1, Image.tupleColumns (tupleColumnsOf ms).2⟩
  ty_app _ _ := refused
  ty_null := refused
  ty_undefined := refused
  ty_number := refused
  ty_bytes := refused
  ty_contextOf _ := refused

/-- The Lean carrier of a type at an identity context. -/
def CarrierAt (L : Leaves) (t : Ty) : Type := (cata_ty (algAt L) t).1

/-- The exact embedding of a type's carrier at an identity context. -/
def imageAt (L : Leaves) (t : Ty) : Image (CarrierAt L t) := (cata_ty (algAt L) t).2

/-- **The carrier algebra of the checked domain**: every identity refused. -/
def alg : TyAlgebra (fun _ => M) := algAt Leaves.refused

/-- The Lean carrier of a type. -/
def Carrier (t : Ty) : Type := (cata_ty alg t).1

/-- The exact embedding of a type's carrier. -/
def image (t : Ty) : Image (Carrier t) := (cata_ty alg t).2

/-- A record's fields: refused at an optional field, or at a field's own refusal. -/
def fieldsRefusal : List (String × Bool × Option String) → Option String
  | [] => none
  | (n, true, _) :: _ => some s!"optional field {n}"
  | (_, false, m) :: rest => m.or (fieldsRefusal rest)

/-- **The refusal fold**: the first reason a type is outside the checked domain, by name. -/
def refusalAlg : TyAlgebra (fun _ => Option String) where
  ty_never := some "never"
  ty_unit := none
  ty_nat := none
  ty_int := none
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
  ty_union a b := a.or b
  ty_lit _ := none
  ty_refOf _ := some "refOf: an identity needs its table"
  ty_deferredOf _ _ := some "deferredOf: an identity needs its table"
  ty_var _ := some "var"
  ty_unknown := some "unknown"
  ty_record fs := if Field.Ascending Field.bytesKey fs then fieldsRefusal fs
    else some "record fields out of canonical order"
  ty_map _ _ := some "map"
  ty_tuple _ := some "tuple"
  ty_app _ _ := some "app"
  ty_null := some "null"
  ty_undefined := some "undefined"
  ty_number := some "number"
  ty_bytes := some "bytes"
  ty_contextOf _ := some "contextOf"

/-- The first reason a type is outside the checked domain; `none` inside it. -/
def refusal (t : Ty) : Option String := cata_ty refusalAlg t

/-- A record's fields are checked: each is required, and its type is in the checked domain. -/
def FieldsChecked : List (String × Bool × Ty) → Prop
  | [] => True
  | (_, o, t) :: rest => o = false ∧ refusal t = none ∧ FieldsChecked rest

theorem fieldsRefusal_of_checked : ∀ fs : List (String × Bool × Ty), FieldsChecked fs →
    fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs) = none
  | [], _ => rfl
  | (_, o, t) :: rest, ⟨ho, ht, hrest⟩ => by
    subst ho
    show (refusal t).or (fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg rest)) =
      none
    rw [ht, fieldsRefusal_of_checked rest hrest]
    rfl

/-- **A record is in the checked domain** when its names ascend and each field is checked. The
deriving step proves a structure's type checked this way: it decides the names' order and
composes each field instance's own proof, so a field instance may be opaque. -/
theorem refusal_record {fs : List (String × Bool × Ty)} (ascending : Field.Ascending Field.bytesKey fs)
    (fields : FieldsChecked fs) : refusal (.record fs) = none := by
  have mapped : Field.Ascending Field.bytesKey
      (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs) := by
    rw [cata_pos_list_prod_string_prod_bool_ty_eq]
    exact List.pairwise_map.mpr ascending
  show (if Field.Ascending Field.bytesKey (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
      then fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
      else some "record fields out of canonical order") = none
  rw [if_pos mapped]
  exact fieldsRefusal_of_checked fs fields

/-- A literal is in the checked domain: its carrier is the unit of its one string. -/
theorem refusal_lit (s : String) : refusal (.lit s) = none := rfl

/-- **A union is in the checked domain** when both sides are. The deriving step of an inductive
proves its type checked this way, one union per constructor but the last. -/
theorem refusal_union {a b : Ty} (ha : refusal a = none) (hb : refusal b = none) :
    refusal (.union a b) = none := by
  show (refusal a).or (refusal b) = none
  rw [ha, hb]
  rfl

/-- An alternative of two refusals is none only when both are. -/
theorem or_eq_none {a b : Option String} (h : a.or b = none) : a = none ∧ b = none := by
  cases a with
  | none => exact ⟨rfl, h⟩
  | some x => cases h

/-- A record with no refusal has fields with no refusal. A step of `expand_of_checked`. -/
theorem fields_checked_of_refusal : ∀ fs : List (String × Bool × Ty),
    fieldsRefusal (fs.map (prodMapSnd (prodMapSnd (cata_ty refusalAlg)))) = none →
      ∀ q ∈ fs, refusal q.2.2 = none
  | [], _ => fun q hq => by cases hq
  | (n, o, t) :: rest, h => by
    cases o with
    | true => cases h
    | false =>
      have h' : (refusal t).or
          (fieldsRefusal (rest.map (prodMapSnd (prodMapSnd (cata_ty refusalAlg))))) = none := h
      have hb := or_eq_none h'
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · rw [hq]
        exact hb.1
      · exact fields_checked_of_refusal rest hb.2 q hq

/-- **A checked code expands to itself under every table**: the checked domain refuses `handle`
and `app`, so a checked code names no declared name. The default proof of
`Modeled.ref_expands` for an unnamed type, whose reference is its code. -/
theorem expand_of_checked (exps : TyDecls) {t : Ty} (h : refusal t = none) :
    Ty.expand exps t = t := by
  induction t with
  | never => rfl
  | unit => rfl
  | nat => rfl
  | int => rfl
  | string => rfl
  | bool => rfl
  | lit s => rfl
  | option inner ih => exact congrArg Ty.option (ih h)
  | list inner ih => exact congrArg Ty.list (ih h)
  | prod a b iha ihb =>
    have hb := or_eq_none h
    show Ty.prod (Ty.expand exps a) (Ty.expand exps b) = _
    rw [iha hb.1, ihb hb.2]
  | union a b iha ihb =>
    have hb := or_eq_none h
    show Ty.union (Ty.expand exps a) (Ty.expand exps b) = _
    rw [iha hb.1, ihb hb.2]
  | record fs ih =>
    have hf : ∀ q ∈ fs, refusal q.2.2 = none := by
      have h' : (if Field.Ascending Field.bytesKey
            (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
          then fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
          else some "record fields out of canonical order") = none := h
      rw [cata_pos_list_prod_string_prod_bool_ty_eq] at h'
      split at h'
      · exact fields_checked_of_refusal fs h'
      · cases h'
    have hm : ∀ gs : List (String × Bool × Ty), (∀ q ∈ gs, Ty.expand exps q.2.2 = q.2.2) →
        gs.map (fun q => (q.1, q.2.1, Ty.expand exps q.2.2)) = gs := by
      intro gs hg
      induction gs with
      | nil => rfl
      | cons q gs ihg =>
        rw [List.map_cons, hg q List.mem_cons_self,
          ihg fun r hr => hg r (List.mem_cons_of_mem q hr)]
    show Ty.record (Ty.expandFields exps fs) = Ty.record fs
    rw [Ty.expandFields_eq_map]
    exact congrArg Ty.record (hm fs fun q hq => ih q hq (hf q hq))
  | _ => cases h

end Model

/-- **A Lean type tied to a checked `Ty`**: an equivalence between the type and the carrier of
`ty`. The image is the fold's, so membership comes from the fold's law and never from the
instance.

`staged` is the fold's image at `ty` written as its combinators: the fold partially evaluated at
a known code. It is the fold's image by definition (`staged_eq`), so it owes no law of its own,
and compiled code runs the combinators with no fold over `Ty` (`docs/research/2026-10-15-modeled-lowering/README.md`).

A named type also has a name in the declaration table (decisions row 402). `decls` holds the
declarations the type brings: each named type it reaches, its own entry last, whose body names
each field's type by its reference. `ref` is the type a program writes: `app n []` for a type
named `n`, the code itself for an unnamed one. `ref_expands` says the reference expands to the
code under every solution of `decls`. Its last premise is `checked`'s statement, which an
unnamed type's default proof reads (`Model.expand_of_checked`). So membership at the name under
the table is membership at the code (`Modeled.memberIn_ref`, `Laws/Schema/Modeled.lean`). An
unnamed type declares nothing, and its reference is its code. -/
class Modeled (α : Type) where
  ty : Ty
  checked : Model.refusal ty = none
  toC : α → Model.Carrier ty
  ofC : Model.Carrier ty → α
  to_of : ∀ c, toC (ofC c) = c
  of_to : ∀ a, ofC (toC a) = a
  staged : Image (Model.Carrier ty) := Model.image ty
  staged_eq : staged = Model.image ty := by rfl
  decls : TyDecls := []
  ref : Ty := ty
  ref_expands : ∀ exps : TyDecls, TyDecls.Expands exps decls → Model.refusal ty = none →
      Ty.expand exps ref = ty := by
    intro exps _ hc
    exact Model.expand_of_checked exps hc

namespace Modeled

/-- The exact embedding of a modeled type: the staged carrier image, across the equivalence. -/
def image (α : Type) [m : Modeled α] : Image α :=
  Image.equiv m.staged m.ofC m.toC m.of_to m.to_of

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

instance : Modeled Unit :=
  ⟨.unit, rfl, id, id, fun _ => rfl, fun _ => rfl, Image.unit, rfl, [], .unit, fun _ _ _ => rfl⟩
instance : Modeled Bool :=
  ⟨.bool, rfl, id, id, fun _ => rfl, fun _ => rfl, Image.bool, rfl, [], .bool, fun _ _ _ => rfl⟩
instance : Modeled Nat :=
  ⟨.nat, rfl, id, id, fun _ => rfl, fun _ => rfl, Image.nat, rfl, [], .nat, fun _ _ _ => rfl⟩
instance : Modeled Int :=
  ⟨.int, rfl, id, id, fun _ => rfl, fun _ => rfl, Image.int, rfl, [], .int, fun _ _ _ => rfl⟩
instance : Modeled String :=
  ⟨.string, rfl, id, id, fun _ => rfl, fun _ => rfl, Image.string, rfl, [], .string,
    fun _ _ _ => rfl⟩

instance {α : Type} [m : Modeled α] : Modeled (List α) where
  ty := .list m.ty
  checked := m.checked
  toC xs := xs.map m.toC
  ofC cs := List.map m.ofC cs
  to_of := list_inv m.toC m.ofC m.to_of
  of_to := list_inv m.ofC m.toC m.of_to
  staged := Image.list m.staged
  staged_eq := congrArg Image.list m.staged_eq
  decls := m.decls
  ref := .list m.ref
  ref_expands exps h _ := Ty.expand_list_eq (m.ref_expands exps h m.checked)

instance {α : Type} [m : Modeled α] : Modeled (Option α) where
  ty := .option m.ty
  checked := m.checked
  toC o := o.map m.toC
  ofC c := Option.map m.ofC c
  to_of := option_inv m.toC m.ofC m.to_of
  of_to := option_inv m.ofC m.toC m.of_to
  staged := Image.option m.staged
  staged_eq := congrArg Image.option m.staged_eq
  decls := m.decls
  ref := .option m.ref
  ref_expands exps h _ := Ty.expand_option_eq (m.ref_expands exps h m.checked)

instance {α β : Type} [ma : Modeled α] [mb : Modeled β] : Modeled (α × β) where
  ty := .prod ma.ty mb.ty
  checked := by
    show (Model.refusal ma.ty).or (Model.refusal mb.ty) = none
    rw [ma.checked, mb.checked]
    rfl
  toC p := (ma.toC p.1, mb.toC p.2)
  ofC c := (ma.ofC c.1, mb.ofC c.2)
  to_of c := Prod.ext (ma.to_of c.1) (mb.to_of c.2)
  of_to p := Prod.ext (ma.of_to p.1) (mb.of_to p.2)
  staged := Image.tuple2 ma.staged mb.staged
  staged_eq := by
    show Image.tuple2 ma.staged mb.staged = Image.tuple2 (Model.image ma.ty) (Model.image mb.ty)
    rw [ma.staged_eq, mb.staged_eq]
  decls := ma.decls ++ mb.decls
  ref := .prod ma.ref mb.ref
  ref_expands exps h _ := Ty.expand_prod_eq (ma.ref_expands exps h.left ma.checked)
    (mb.ref_expands exps h.right mb.checked)

end Modeled
end Effect4.Schema
