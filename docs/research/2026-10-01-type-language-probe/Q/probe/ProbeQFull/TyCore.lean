/-!
# ProbeQFull.TyCore — the variant probe copy of `Effect4.Program.Ty`'s declaration, with `record` appended

Seat Q, type-language probe (2026-10-01). A copy of the inductive at
`src/Effect4/Program/Ty.lean:37-75` (base `bff50631`), constructors in the same order with the
same field names, plus the data wave's variant: the record with the optional modifier inside its field list
(wire tag 20) and a keyed map (wire tag 21):

    | record (fields : List (String × Ty × Bool))
    | map (key value : Ty)

The declaration sits alone in this module because Lean 4.33.1 derives no `DecidableEq` for a
nested inductive (`Lean/Elab/Deriving/DecEq.lean`: `if indVal.isNested then return false`), and
`Ty.lean` needs `DecidableEq Ty` before its first function (`insertMember` `if t = u`, `sub`
`if a = b`, `Effect4.Row.normalize`'s `[DecidableEq α]`). A generated equality therefore lands
in a module between the declaration and the functions: here `ProbeQFull.TyEq`, written by the
probe's generator `Q/tools/Effect4Gen/Elim.lean`.

The namespace is `ProbeQFull` so the generators' names (`TyFam`, `TyAlgebra`, `cata_ty`, `Ty.args`,
…) land under `ProbeQFull` exactly as they land under `Effect4.Program` in the tree.
-/

namespace ProbeQFull

inductive Ty
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | except (error value : Ty)
  | exitOf (value error : Ty)
  | causeOf (error : Ty)
  | fiberOf (value error : Ty)
  | union (left right : Ty)
  | lit (value : String)
  | refOf (value : Ty)
  | deferredOf (value error : Ty)
  | var (index : Nat)
  | unknown
  /-- The data wave's variant of row 119: each field `(name, type, optional)`; an optional
  field is `a?: τ` (stage 4's modifier carried inside the record's field list). -/
  | record (fields : List (String × Ty × Bool))
  /-- Row 125's keyed map, a plain two-child head. -/
  | map (key value : Ty)

end ProbeQFull
