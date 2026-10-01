/-!
# ProbeQ.TyCore — the probe copy of `Effect4.Program.Ty`'s declaration, with `record` appended

Seat Q, type-language probe (2026-10-01). A copy of the inductive at
`src/Effect4/Program/Ty.lean:37-75` (base `bff50631`), constructors in the same order with the
same field names, plus the row-119 constructor appended last (wire tag 20):

    | record (fields : List (String × Ty))

The declaration sits alone in this module because Lean 4.33.1 derives no `DecidableEq` for a
nested inductive (`Lean/Elab/Deriving/DecEq.lean`: `if indVal.isNested then return false`), and
`Ty.lean` needs `DecidableEq Ty` before its first function (`insertMember` `if t = u`, `sub`
`if a = b`, `Effect4.Row.normalize`'s `[DecidableEq α]`). A generated equality therefore lands
in a module between the declaration and the functions: here `ProbeQ.TyEq`, written by the
probe's generator `Q/tools/Effect4Gen/Elim.lean`.

The namespace is `ProbeQ` so the generators' names (`TyFam`, `TyAlgebra`, `cata_ty`, `Ty.args`,
…) land under `ProbeQ` exactly as they land under `Effect4.Program` in the tree.
-/

namespace ProbeQ

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
  /-- Row 119: a record type, its fields named; canonical order is by the name's UTF-8 bytes. -/
  | record (fields : List (String × Ty))

end ProbeQ
