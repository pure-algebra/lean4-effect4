/-!
# GenFix.Wave.TyCore — the data wave's whole `Ty` append, on a fixture

Today's twenty constructors (`src/Effect4/Program/Ty.lean`, base `74dae8d2`, same order and field
names), then the eight the wave appends in probe T's commit-4 order (probe Q's `ProbeQW`):
`record (fields : List (String × Ty × Bool))` (probe Q's field shape `(name, type, optional)`;
probe P's copy writes `(name, optional, type)`, which commit 4 fixes), `map`, `tuple`, `app`, and
the leaves `null`, `undefined`, `number`, `bytes`. Three heads have variable arity (`record`,
`tuple`, `app`), so the family is nested and its companions are generated
(`GenFix.Wave.TyEq`, the `elim` kind); `app`'s declared variances are the variances producer's
core module (`GenFix.Wave.TyVariance`, `--lean-out`). Read by `scripts/test-generators.py`.
-/

namespace GenFix.Wave

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

end GenFix.Wave
