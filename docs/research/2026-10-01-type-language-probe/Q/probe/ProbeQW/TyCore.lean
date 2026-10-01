/-!
# ProbeQW.TyCore — the data wave's whole `Ty` append, on a copy

Seat Q probe (2026-10-01), after seat T's census (`T/note.md` §2.1, §2.4 commit 4): today's 20
constructors (`src/Effect4/Program/Ty.lean:37-75`, same order, same field names), then every
constructor the wave appends, in commit 4's order (wire tags 20–27):

* `record (fields : List (String × Ty × Bool))`: a field `(name, type, optional)`, the
  optional modifier inside the field list (seat P's `(name, τ, optional)`; the exact field shape
  is P's to fix);
* `map (key value : Ty)`: row 125, a plain two-child head;
* `tuple (items : List Ty)`: any arity, no names, position is the order;
* `app (name : String) (args : List Ty)`: a nominal reference, each argument at its declared
  variance (read by name from the generated `ProbeQW.TyVariance`);
* `null`, `undefined`, `number`, `bytes`: leaves.

Three of the eight are nested variable-arity heads (`record`, `tuple`, `app`); the declaration is
alone in this module for the reason `ProbeQ.TyCore` gives.
-/

namespace ProbeQW

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
  | record (fields : List (String × Ty × Bool))
  | map (key value : Ty)
  | tuple (items : List Ty)
  | app (name : String) (args : List Ty)
  | null
  | undefined
  | number
  | bytes

end ProbeQW
