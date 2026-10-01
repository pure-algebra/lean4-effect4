import ProbeU.ClassesTable

/-!
# Probe U — the classifier table of `Ty` (family (b)): one Boolean column per question

The per-constructor answers five hand traversals restate today, each in its own twenty-arm
match: is this node a template parameter (`Ty.closed`, `Ty.varsOf`), does it hold no handle
(`handleFreeAlg`), does the JSON codec have an arm for it (`Codec.isSupported`), may a template
parameter sit below it and still be read by inference (`valueVarsAlg`), and does inference
read its children positionally (`Ty.templateAdmissible`, which refuses a parameter under a
union head). Written as one table, a row per constructor: a new constructor is one row, and
each column is answered there or the table does not compile. No catch-all anywhere, so no
answer is given by default (decisions row 56's rule, met by construction rather than by
review).

The table is data: `U/tables/ty-classes.json`, emitted as `tyClasses` by the table emitter
(`U/patches/TableGen.lean`) into `U/generated/ProbeU/ClassesTable.lean`; the row type is
`ProbeU/ClassRow.lean`. The generic folds that read the columns are below, and their agreement
with today's definitions is in `U/probes/MonoidFolds.lean`.
-/

set_option autoImplicit false

namespace ProbeU

open Effect4.Program

/-! ## The generic folds over a column -/

/-- **Every node in a class**: the monoid fold `(Bool, &&, true)` of a column. -/
def allHeads (col : ClassRow → Bool) : TyAlgebra (fun _ => Bool) :=
  TyAlgebra.headAlg (· && ·) fun c _ => col (tyClasses.get c)

/-- **The parameters, in occurrence order**: the monoid fold `(List Nat, ++, [])` of the
`param` column at the payload. -/
def paramsAlg : TyAlgebra (fun _ => List Nat) :=
  TyAlgebra.headAlg (· ++ ·) fun c l =>
    bif (tyClasses.get c).param then (match l with | .nat i => [i] | _ => []) else []

/-- **Parameters only below heads of a class**: the pair (no parameter at all, parameters only
below heads where `ok` holds), one layer at a time. Below a head outside the class the children
must be closed. -/
def varsUnderLayer (ok : ClassRow → Bool) : TyCtor → TyLeaf → List (Bool × Bool) → Bool × Bool
  | c, _, [] => (!(tyClasses.get c).param, true)
  | c, _, [a] => (a.1, bif ok (tyClasses.get c) then a.2 else a.1)
  | c, _, [a, b] => (a.1 && b.1, bif ok (tyClasses.get c) then a.2 && b.2 else a.1 && b.1)
  | _, _, _ => (true, true)

def varsUnder (ok : ClassRow → Bool) : TyAlgebra (fun _ => Bool × Bool) :=
  TyAlgebra.ofLayer (varsUnderLayer ok)

/-- **The first node of a class, located**: the path to the first node `hit` holds of, each
child reached at its binder's name (the constructor's own field names, read off the
declaration). -/
def firstLayer (hit : TyCtor → TyLeaf → Bool) :
    TyCtor → TyLeaf → List (List String → Option (List String)) → List String → Option (List String)
  | c, l, [], pos => if hit c l then some pos else none
  | c, l, [a], pos => if hit c l then some pos else a (pos ++ [(c.binders).getD 0 ""])
  | c, l, [a, b], pos =>
    if hit c l then some pos
    else a (pos ++ [(c.binders).getD 0 ""]) <|> b (pos ++ [(c.binders).getD 1 ""])
  | _, _, _, _ => none

def firstAlg (hit : TyCtor → TyLeaf → Bool) : TyAlgebra (fun _ => List String → Option (List String)) :=
  TyAlgebra.ofLayer (firstLayer hit)

end ProbeU
