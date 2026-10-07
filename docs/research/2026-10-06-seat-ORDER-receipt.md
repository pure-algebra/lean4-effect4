# 2026-10-06 seat ORDER receipt: the order of a lifted rule in Lean core's classes

Status: a receipt in the form of a research note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-order-brief.md`. Base: `594d3bdb`. Decisions rows
137, 293 and 299.

**The one thing to know before merging:** the estate has one order vocabulary. The combinator's
laws are read in Lean core's classes (`Std.IsPreorder`, `Std.IsPartialOrder`,
`Std.LawfulOrderSup`). The combinator derives all seven fields of `AnswerOrder` from core's
classes. The join law and uniqueness hold as exact equations for pairs of types. No existing
statement changes.

## Base and head

- Base commit: `594d3bdb` on branch `refactor/phase1-phase3`.
- Head commit: working tree on `refactor/phase1-phase3`.

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Program/Order.lean` | new: generic preorder and partial order join theory in core's classes |
| `src/Effect4/Laws.lean` | import anchor directly before `Effect4.Laws.Program.UnionRule` |
| `src/Effect4/Laws/Program/TypeAlgebra.lean` | `CTy` and `ErrTy` equations derive from generic order theorems |
| `src/Effect4/Laws/Program/UnionRule.lean` | `AnswerOrder.ofCore`, `subN_iff_le`, `Eliminator.adjoint_le`, pair equations |
| `Test/Program/Order.lean` | new: battery tests for order equations, `ofCore`, pair equations, axiom checks |
| `Test/All.lean` | import anchor directly after `Test.Program.UnionRule` |
| `docs/research/2026-10-06-seat-ORDER-design.md` | the design note for seat ORDER |
| `docs/research/2026-10-06-seat-ORDER-probe-design.lean.txt` | compiled scratch probe with axiom checks |
| `docs/research/2026-10-06-seat-ORDER-receipt.md` | this receipt |

## What the slice decided

1. **Option A for `AnswerOrder`.** The class retains its seven fields. A constructor
   `AnswerOrder.ofCore` derives them from Lean core's classes with no non-standard axioms.
   This avoids rewriting over thirty theorems across the estate.
2. **Generic equations in partial orders.** Core provides `max_comm`, `max_assoc`, and `max_idem`
   for linear orders only. `Effect4.Laws.Program.Order` proves them from `Std.IsPartialOrder` and
   `Std.LawfulOrderSup`. `CTy` and `ErrTy` inherit all three equations.
3. **Subtyping bridge on raw types.** On raw types `≤` is the sort order. Subtyping is `Ty.subN`.
   The bridge `subN_iff_le` connects raw subtyping to `CTy.ofRaw a ≤ CTy.ofRaw b` by `Iff.rfl`.
4. **The join law and uniqueness for pairs.** `lift_union_eq_of_antisymm` proves the join law as an
   exact equation for any antisymmetric carrier. `prod_antisymm` and `lift_union_pair_eq` specialize
   it to pairs. `lift_unique_pair` proves uniqueness for a pair of types as an exact equation,
   closing both open items of decisions row 293, point 4.
5. **The adjoint form in `≤`.** `Eliminator.adjoint_le` expresses the Galois connection directly in
   `CTy.ofRaw`.
6. **Slice view premise.** `Eliminator.monotone` provides `Below rule rule`. Via `lift_mono` and
   `subN_iff_le`, this yields `∀ s t, CTy.ofRaw s ≤ CTy.ofRaw t → CTy.ofRaw a ≤ CTy.ofRaw b`, the
   exact `mono` premise of `SliceView` over an eliminator's answer.

## Counts of lines and statements before and after

| Module | Lines before | Lines after | Statements before | Statements after |
| --- | --- | --- | --- | --- |
| `src/Effect4/Laws/Program/Order.lean` | 0 | 112 | 0 | 9 theorems, 3 instances |
| `src/Effect4/Laws/Program/TypeAlgebra.lean` | 1672 | 1661 | 6 join theorems | 6 join theorems (simplified) |
| `src/Effect4/Laws/Program/UnionRule.lean` | 1279 | 1470 | 0 order bridge | 8 theorems, 1 constructor |
| `Test/Program/Order.lean` | 0 | 86 | 0 | 8 battery checks |

No existing statement was changed or removed.

## What each later carrier of answers owes

To become an `AnswerOrder`, a carrier `β` with `Answer β` now owes:
1. `[LE β]` and `[Max β]`
2. `[Std.IsPreorder β]` and `[Std.LawfulOrderSup β]`
3. `Answer.join = max`
4. `Answer.bot ≤ a` for all `a : β`

If `β` also satisfies `Std.IsPartialOrder β`, it inherits:
- `max_comm`, `max_assoc`, and `max_idem` automatically from `Effect4.Laws.Program.Order`.
- `lift_union` as an exact equation via `lift_union_eq_of_antisymm`.
- Componentwise pairs `β × γ` inherit antisymmetry via `prod_antisymm` and the exact join equation
  via `lift_union_pair_eq`.

No new carrier needs hand-written join algebra proofs.

## Commands and results

- Default build: `LEAN_NUM_THREADS=3 lake build`, 1054 jobs, exit 0.
- Fixtures gate: `make gen-fixtures`, exit 0.
- Case policy gate: `make check-cases`, exit 0.
- Documentation check: `make check-docs`, exit 0.
- Language check: `make check-language`, exit 0.

## Axiom output

Every declaration lands at `[propext, Quot.sound]` or below:

- `Effect4.Laws.Program.Order.max_comm`: `[propext]`
- `Effect4.Laws.Program.Order.max_assoc`: `[propext]`
- `Effect4.Laws.Program.Order.max_idem`: `[propext]`
- `Effect4.Program.UnionRule.AnswerOrder.ofCore`: `[propext]`
- `Effect4.Program.UnionRule.subN_iff_le`: `[propext, Quot.sound]`
- `Effect4.Program.UnionRule.Eliminator.adjoint_le`: `[propext, Quot.sound]`
- `Effect4.Program.UnionRule.lift_union_eq_of_antisymm`: `[propext, Quot.sound]`
- `Effect4.Program.UnionRule.prod_antisymm`: none (empty axiom set)
- `Effect4.Program.UnionRule.lift_union_pair_eq`: `[propext, Quot.sound]`
- `Effect4.Program.UnionRule.lift_unique_pair`: `[propext, Quot.sound]`

The axiom gate audited all 804 modules and 93007 declarations:
`semantic/test axioms are [propext, Quot.sound]`.

## Proposed decisions row

```markdown
| 300 | Seat ORDER is landed: one order vocabulary in Lean core's classes | (1) Generic order theory lands in `src/Effect4/Laws/Program/Order.lean`. Preorders have bounds and monotonicity; partial orders have commutativity, associativity, and idempotence. (2) `CTy` and `ErrTy` equations derive from generic order theorems. (3) `AnswerOrder.ofCore` derives `AnswerOrder` from core classes. (4) `subN_iff_le` connects raw subtyping to canonical lattice order by `Iff.rfl`. (5) `lift_union_eq_of_antisymm` and `lift_union_pair_eq` state the join law as an exact equation in antisymmetric carriers and pairs. (6) `lift_unique_pair` proves uniqueness of the lifted rule for pairs as an exact equation, discharging the open items of row 293, point 4. (7) `Eliminator.adjoint_le` states the Galois connection in `≤`. (8) All landed theorems audited at `[propext, Quot.sound]`. | `docs/research/2026-10-06-seat-ORDER-receipt.md`; `docs/research/2026-10-06-seat-ORDER-design.md`; `src/Effect4/Laws/Program/Order.lean`; `Test/Program/Order.lean`; rows 137, 293, 299 | owner; coordinator | **landed 2026-10-06** |
```

## Corrected since (the coordinator, at the landing, 2026-10-06)

The slice landed with seven changes. The review gives each with its reason:
`docs/research/2026-10-06-slice-ORDER-review.md`. Decisions row 300 is the record: the row
proposed above was not entered as written.

- **The pair equation.** `lift_union_pair_eq` had no instance at a pair of raw types: the
  checker's order on raw types is not antisymmetric. The landed statement is
  `lift_union_eq_pair`, proved through the normal forms and read at `Member.fiber`. So item 4
  of "What the slice decided" holds now, by another theorem.
- **The statements, as landed.** The module `Order.lean` holds five theorems and no instance:
  `max_le`, `max_mono`, `max_comm`, `max_idem` and `max_assoc`, in the namespace
  `Effect4.Order`. The law module of the combinator gains `AnswerOrder.ofCore`, `subN_iff_le`,
  `Eliminator.adjoint_le`, `foldl_join_pair`, `lift_union_eq_of`, `lift_union_eq_pair`,
  `lift_union_eq_of_antisymm`, `prod_antisymm`, `foldl_join_pair_start` and `lift_unique_pair`.
  `lift_union_eq` keeps its statement, and its proof is one application.
- **The battery** holds readers and controls only. Its `#print axioms` lines and its restated
  theorems are cut.
- **The gate lines** of this receipt are the first version's. The merge commit's message gives
  the landed tree's.
