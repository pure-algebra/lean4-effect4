import Effect4.Program.Typed
import Effect4.Program.Fold

/-!
# Program.Columns — the scans of one type column

Three scans of one raw type, each run before normalization can discard syntax:

* `findInt`: the first occurrence of the reserved integer constructor (DB-15, DI-67), with its
  path.
* `findInternalHandle`: the first internal handle kind, with its path (decisions row 97 interim).
* `admitColumn`: the column is the designed bottom or has a member (`inhabited`, rows 127 and
  149).

The signature's admission reads each of them at the root of every row column (`rowChecks`,
`Program/SigApp.lean`). Program admission reads `findInt` and `admitColumn` at the program's own
columns, and `findInt` at the raw table (`Program/Admission.lean`).

The module is not a Lean module (decisions row 200): `findInternalHandle` reads
`internalHandleTargets`, which `Program/Typed.lean` defines beside the membership arms that read
the same spellings, and `Program/Typed.lean` is one of decisions row 202's specialization sites,
which stay non-module.
-/

namespace Effect4.Program

/-- A boundary field path, with decimal positions for table rows. -/
abbrev Path := List String

mutual
/-- First occurrence of the reserved integer constructor in a raw type. -/
def findInt (pos : Path) : Ty → Option Path
  | .int => some pos
  | .option t | .list t => findInt (pos ++ ["inner"]) t
  | .causeOf e => findInt (pos ++ ["error"]) e
  | .prod a b | .union a b =>
      findInt (pos ++ ["left"]) a <|> findInt (pos ++ ["right"]) b
  | .except e a => findInt (pos ++ ["error"]) e <|> findInt (pos ++ ["value"]) a
  | .exitOf a e | .fiberOf a e | .deferredOf a e =>
      findInt (pos ++ ["value"]) a <|> findInt (pos ++ ["error"]) e
  | .refOf a => findInt (pos ++ ["value"]) a
  | .map k v => findInt (pos ++ ["key"]) k <|> findInt (pos ++ ["value"]) v
  | .record fs => findIntFields pos fs
  | .tuple ts | .app _ ts => findIntItems pos 0 ts
  | .never | .unknown | .unit | .nat | .string | .bool | .handle _ | .lit _ | .var _
  | .null | .undefined | .number | .bytes => none
/-- The field-list companion of `findInt`: a field at its name. -/
def findIntFields (pos : Path) : List (String × Bool × Ty) → Option Path
  | [] => none
  | (n, _, t) :: rest => findInt (pos ++ [n]) t <|> findIntFields pos rest
/-- The item-list companion of `findInt`: an item at its decimal position. -/
def findIntItems (pos : Path) (i : Nat) : List Ty → Option Path
  | [] => none
  | t :: rest => findInt (pos ++ [toString i]) t <|> findIntItems pos (i + 1) rest
end

/-- Inhabitance as a fold (decisions row 127; DI-67): `never` and a template parameter have no
member; a product needs both columns, a result or a union either, a tuple every item, a record
every canonical field that is not optional (an absent optional field is a member's, decisions row
157); every other former has a member at every argument in some world (`none`, `[]`, a failure
with no typed reason, the empty cause, a declared handle, the empty map, an integer, the leaves). The laws are `Laws/Program/Typed/Membership.lean`'s:
`inhabited_iff_fits` (agreement with `Fits` on every type, one world for every handle position by
fresh keys), `inhabited_of_hasTy` (sound against DI-67's `Val.hasTy`),
`fits_of_inhabited_handleFree` (a world-free witness on the data fragment) and the handle
witnesses. -/
def inhabitedAlg : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := true
  ty_string := true
  ty_bool := true
  ty_handle _ := true
  ty_option _ := true
  ty_list _ := true
  ty_prod a b := a && b
  ty_except e a := e || a
  ty_exitOf _ _ := true
  ty_causeOf _ := true
  ty_fiberOf _ _ := true
  ty_union l r := l || r
  ty_lit _ := true
  ty_refOf _ := true
  ty_deferredOf _ _ := true
  ty_var _ := false
  ty_unknown := true
  ty_record fs := (Ty.canon fs).all fun p => p.2.1 || p.2.2
  ty_map _ _ := true
  ty_tuple ts := ts.all id
  ty_app _ _ := true
  ty_null := true
  ty_undefined := true
  ty_number := true
  ty_bytes := true

/-- Whether a type has a member (`inhabitedAlg`). -/
def inhabited (t : Ty) : Bool := cata_ty inhabitedAlg t

/-- A column admission accepts (row 127): the designed bottom, canonical `never`, or a type with
a member. `prod never nat` and `except never never` are canonical, not `never`, and empty, so
they are refused; `list int` has a member and is the `int` scan's to refuse (DB-15), not this
check's. -/
def admitColumn (t : Ty) : Bool := t.normalize == .never || inhabited t

/-- Locate internal handle types with the generated type fold. Raw syntax is inspected
before normalization, including every nested answer and error column. -/
def internalHandleScan : TyAlgebra (fun _ => Path → Option Path) where
  ty_never := fun _ => none
  ty_unit := fun _ => none
  ty_nat := fun _ => none
  ty_int := fun _ => none
  ty_string := fun _ => none
  ty_bool := fun _ => none
  ty_handle target := fun pos => if internalHandleTargets.contains target then some pos else none
  ty_option inner := fun pos => inner (pos ++ ["inner"])
  ty_list inner := fun pos => inner (pos ++ ["inner"])
  ty_prod left right := fun pos => left (pos ++ ["left"]) <|> right (pos ++ ["right"])
  ty_except error value := fun pos => error (pos ++ ["error"]) <|> value (pos ++ ["value"])
  ty_exitOf value error := fun pos => value (pos ++ ["value"]) <|> error (pos ++ ["error"])
  ty_causeOf error := fun pos => error (pos ++ ["error"])
  ty_fiberOf _ _ := some
  ty_union left right := fun pos => left (pos ++ ["left"]) <|> right (pos ++ ["right"])
  ty_lit _ := fun _ => none
  ty_refOf _ := some
  ty_deferredOf _ _ := some
  ty_var _ := fun _ => none
  ty_unknown := fun _ => none
  ty_record fs := fun pos => fs.foldr (fun p acc => p.2.2 (pos ++ [p.1]) <|> acc) none
  ty_map key value := fun pos => key (pos ++ ["key"]) <|> value (pos ++ ["value"])
  ty_tuple items := fun pos =>
    items.zipIdx.foldr (fun p acc => p.1 (pos ++ [toString p.2]) <|> acc) none
  -- a nominal reference is the handle at its name (its arguments are unread by membership)
  ty_app name _ := fun pos => if internalHandleTargets.contains name then some pos else none
  ty_null := fun _ => none
  ty_undefined := fun _ => none
  ty_number := fun _ => none
  ty_bytes := fun _ => none

/-- The first internal handle kind in a raw type, at its path from `pos` (`internalHandleScan`).
Requests may pass internal handles outward; a host answer or error column may not introduce one
until its declaration registry is available (row 97 interim). -/
def findInternalHandle (pos : Path) (ty : Ty) : Option Path :=
  cata_ty internalHandleScan ty pos

end Effect4.Program
