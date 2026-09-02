# Semantics cause and exit attacks

These attacks belong to the `Effect4.Cause` / `Effect4.Exit` first-order data
packet frozen by [`test/contracts/cause-exit.contract.md`](../../contracts/cause-exit.contract.md)
and [`docs/CAUSE-DAG.md`](../../../docs/CAUSE-DAG.md). Stable IDs live in
[`../REGISTER.md`](../REGISTER.md); the executable Lean witnesses live in
`Effect4Test/Counterexamples/Semantics/CauseExit.lean` and are a self-contained
breaker model that stays green while the production surface is absent.

The pinned source is `effect@4.0.0-rc.112` under
`vendor/effect-4.0.0-rc.112/src/`.

## E4-SEM-CE-001 — tree-shaped cause

- **BROKE:** a richer cause carrier with sequential and parallel composition
  nodes faithfully refines rc.112's cause.
- **WITNESS:** `tree_invents_structure` — `sequential (leaf a) (leaf b)` and
  `parallel (leaf a) (leaf b)` are distinct trees with the same flattening, so
  the node is unobservable. `tree_empty_not_unique` — the tree also gives the
  empty cause more than one spelling.
- **CLASS:** invented structure.
- **FIXED-BY:** `Cause` is a structure with one `reasons : List (Reason …)`
  field; `Cause.ext` makes that list the whole content and
  `Cause.combine_no_new_reason` forbids combine from introducing a node.
  Census rows `cause.flat-reasons`, `rule.cause-has-no-structure`.

## E4-SEM-CE-002 — combine as concatenation

- **BROKE:** `causeCombine` is `self ++ that`.
- **WITNESS:** `append_duplicates_reasons` — concatenating `[a]` with `[a, b]`
  repeats `a`, which `Arr.union` does not. `append_breaks_self_combine` —
  concatenation also destroys the structural short circuit, so `combine a a = a`
  fails while the union keeps it.
- **CLASS:** lost deduplication.
- **FIXED-BY:** `Cause.dedup` with both frozen equations, `Cause.combine_reasons`
  for the definition-level law, `Cause.combine_order` for the `Arr.union` order,
  and `Cause.combine_self` for the short circuit. Census row
  `cause.combine-union`.

## E4-SEM-CE-003 — positional squash

- **BROKE:** `causeSquash` may report whichever reason comes first in the list,
  or may prefer a defect that appears before a typed error.
- **WITNESS:** `squash_must_partition_before_choosing` — on `[die 1, fail 1]`
  the positional squash answers `defect 1` where rc.112 answers `error 1`.
  `squash_interrupt_does_not_shadow_defect` — the same failure with an
  interruption before a defect. `squash_empty_is_a_fourth_arm` — an empty cause
  and an interrupt-only cause squash to different values, so the arm count is
  four, not three.
- **CLASS:** arm-selection order.
- **FIXED-BY:** `Cause.squash_error`, `Cause.squash_defect`,
  `Cause.squash_interrupted`, `Cause.squash_empty`,
  `Cause.squash_emptyCause_iff`, and the ground receipt
  `Cause.squash_fail_over_die`. The arms are stated as partition tests, not
  positional tests. Census row `cause.squash`; see the census-summary note in
  `docs/CAUSE-DAG.md` for the fourth arm.

## E4-SEM-CE-004 — silent annotation overwrite

- **BROKE:** merging annotations lets the incoming map win, or moves an
  overwritten key to the end of the map.
- **WITNESS:** `annotate_must_not_overwrite_by_default` — the overwriting merge
  reports `2` for a key whose first recorded value was `1`.
  `annotate_overwrite_keeps_position` — even with `overwrite := true` the two
  merges differ, because rc.112's `new Map(this.annotations)` then `set` keeps
  the key's slot while the rejected merge appends it.
  `annotate_empty_is_identity` — the `size === 0` guard is observable.
- **CLASS:** lost annotation, lost order.
- **FIXED-BY:** `ReasonAnnotations.annotate_entries` freezes the exact merge
  shape; `lookup_annotate_kept`, `lookup_annotate_new`,
  `lookup_annotate_overwrite`, `lookup_annotate_absent`, `annotate_keys`, and
  `annotate_empty` freeze the observations. Census row `cause.annotations`;
  the WeakMap trigger is refused under `CAUSE-FB-WEAKMAP`.

## E4-SEM-CE-005 — finalizer failure under a successful exit

- **BROKE:** a finalizer failure may be discarded in favour of the original
  exit, or the original exit cause may be re-raised by the merge itself.
- **WITNESS:** `finalizer_failure_stands_alone` — the exit-wins merge answers
  `success` where rc.112 answers `failure [finalizerCause]`.
  `successful_finalizer_under_failed_exit` — with a failed exit and a
  successful finalizer, `combineFinalizerCause` is the *successful* effect;
  restoring the original exit is the caller's `flatMap`, not this combinator's
  job.
- **CLASS:** lost failure, misplaced responsibility.
- **FIXED-BY:** four exact `Exit.mergeFinalizer_*` arms transcribed from
  `internal/effect.ts:3800-3804`, plus three `Exit.restoreAfterFinalizer_*`
  arms for the caller-side composite at `internal/effect.ts:4023-4028`. Census
  row `cause.finalizer-merge`.

## E4-SEM-CE-006 — any failed exit fails the join

- **BROKE:** `exitAsVoidAll` fails whenever any input exit is a `Failure`.
- **WITNESS:** `empty_cause_failure_joins_to_success` — a `Failure` carrying an
  empty cause contributes no reason, so the pinned join succeeds while the
  naive join returns `Failure []`. `join_is_not_combine` — the join
  concatenates and keeps duplicates, so it is not `causeCombine` applied
  pairwise.
- **CLASS:** wrong emptiness test.
- **FIXED-BY:** `Exit.asVoidAll_reasons` fixes the concatenation exactly,
  `Exit.asVoidAll_empty_cause` and `Exit.asVoidAll_keeps_duplicates` pin the
  two sharp consequences, and `Exit.asVoidAll_all_success` covers the census
  clause. Adjacent census row `scope.exit-as-void-all`.

## E4-SEM-CE-007 — a cause as a canonical finite set

- **BROKE:** `Effect4.Data.Row`, the repository's canonical finite-set carrier,
  can carry a cause because combine is a set union.
- **WITNESS:** `union_is_not_commutative` — `union [a] [b]` and `union [b] [a]`
  are member-equivalent but unequal, and `Row` would identify them.
  `order_changes_squash` — the two orders squash to different errors, so order
  is not a presentation detail.
- **CLASS:** over-canonicalization.
- **FIXED-BY:** `Cause` retains an ordered `List`, `Cause.combine_order` states
  the operand-order-preserving union, and `docs/CAUSE-DAG.md` separation 2
  records that `Row` is not reused. Census rows `cause.combine-union`,
  `cause.squash`.
