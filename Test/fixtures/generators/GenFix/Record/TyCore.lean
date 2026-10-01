/-!
# GenFix.Record.TyCore — today's `Ty` with a field-list constructor appended (a generator fixture)

A copy of `Effect4.Program.Ty` (`src/Effect4/Program/Ty.lean`, base `74dae8d2`): the twenty
constructors in their order with their field names, plus row 119's constructor appended last,

    | record (fields : List (String × Ty))

which makes the family nested. Lean 4.33.1 derives no `DecidableEq` for a nested inductive and
`induction` refuses one, so the companions are generated: `tools/Effect4Gen/Fold.lean
--kind GenFix.Record.Ty=elim` writes `GenFix.Record.TyEq` (the eliminator, the equality and the
`Repr`) between this declaration and its functions (`GenFix.Record.Ty`). Probe Q's family
(`docs/research/2026-10-01-type-language-probe/Q/probe/ProbeQ/TyCore.lean`), renamed.

Read by `scripts/test-generators.py`; not a battery module (`Test/fixtures/` is outside the
module-closure gate, `Test/Audit/AxiomGate.lean:348-353`).
-/

namespace GenFix.Record

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

end GenFix.Record
