# Semantics cause and exit attacks

These attacks belong to the `Effect4.Cause` / `Effect4.Exit` first-order data
packet frozen by [`Test/contracts/cause-exit.contract.md`](../../contracts/cause-exit.contract.md)
and [`docs/research/CAUSE-DAG.md`](../../../docs/CAUSE-DAG.md). Stable IDs live in
[`../REGISTER.md`](../REGISTER.md); the executable Lean witnesses live in
`Test/Counterexamples/Machine/Semantics/CauseExit.lean` and are a self-contained
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
  `docs/research/CAUSE-DAG.md` for the fourth arm.

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
  the operand-order-preserving union, and `docs/research/CAUSE-DAG.md` separation 2
  records that `Row` is not reused. Census rows `cause.combine-union`,
  `cause.squash`.

## E4-SEM-CE-008 — a host-spelled mask table

- **BROKE:** the host harness carrying its own list of masks, or comparing raw
  traces, so that "agreement" drifts from the Lean projection.
- **WITNESS:** `git:c407ab7:scripts/test-trace-goldens-gate.sh` mutant `removed-masks`: a
  mask table without rows is refused as `mask table drift`;
  `agreement_is_per_mask` in lean4-effects shows two traces equal under `m1`
  and different raw.
- **CLASS:** claim scope.
- **FIXED-BY:** `git:c407ab7:generated/traces/masks.tsv` is a projection of
  `Effect4.Trace.maskTable`; `effect4-trace` projects both sides with that
  table and reports per mask.

## E4-SEM-CE-009 — an answer encoded from its runtime value

- **BROKE:** encoding a host answer from whatever value the runtime hands back.
- **WITNESS:** the first host run of `harness/trace`: rc.112's `Ref.set`
  returns the underlying mutable ref under a declared `Effect<void>`; the
  untyped encoder threw inside the tracer and the trace ended in
  `done {"failure":[]}` instead of `answer put []`.
- **CLASS:** declared-versus-actual host type.
- **FIXED-BY:** `ServiceRow.rowsDecl` carries each operation's answer spelling
  and `wireAnswer` records a `void` answer as unit; `docs/research/TRACE-DAG.md`
  separation 7.

## E4-SEM-CE-016 — a memoized rebuild as a second construction

- **BROKE:** reading `build` as "run the layer", so every build constructs,
  answers a fresh handle, and raises the construction count.
- **WITNESS:** `git:c407ab7:Effect4Test/Counterexamples/Semantics/Layers.lean`: a memo hit
  leaves the store untouched and answers the handle already bound. The
  `buildMemo` golden is two builds and one handle; `freshRebuild` and
  `freshRegion` are the contrast that makes it a choice, because layer 3 is
  `Layer.fresh` of layer 1 — a distinct layer identity, never memoized — and
  answers two handles, two layer scopes, and a count of two against layer 1.
- **CLASS:** identity confusion (a layer value versus a construction).
- **FIXED-BY:** `build` answers the memo table when the layer is memoized and
  the scope is open; only a construction raises `provideCount` or takes a
  handle. `git:c407ab7:harness/trace/layer-tail.ts` reads both back off rc.112: the memo
  entry replays the built context, and the *service* object inside it is the
  identity — the `Context` wrapper is not, because `buildWithMemoMap` maps
  `Context.add(CurrentMemoMap, …)` over it on every build. Census rows
  `layer.memo-build-once`, `layer.memo-get-or-else`,
  `layer.build-with-memo-map-service`, `layer.fresh-drops-memoization`.

## E4-SEM-CE-017 — release in construction order

- **BROKE:** releasing constructed layers in the order they were built, or
  leaving the order unstated because "a scope closes what it owns".
- **WITNESS:** `git:c407ab7:Effect4Test/Counterexamples/Semantics/Layers.lean`: `close`
  answers `live.reverse`, and on three live layers that list differs from the
  construction order. The `releaseOrder` and `freshRelease` goldens answer
  `[1, [0, []]]`, and the host agrees under `outcome`, `m1` and `m2` at a large
  `MaxOpsBeforeYield` and at the rc.112 floor of 3.
- **CLASS:** unstated order.
- **FIXED-BY:** rc.112 registers each memo entry's finalizer on the caller
  scope before running the construction and a scope runs its finalizers in
  reverse registration order, so the last layer built is the first released.
  Census rows `layer.memo-build-once`, `layer.memo-finalizer-last-observer`.

## E4-SEM-CE-018 — `close` as a memo-table reset

- **BROKE:** treating `close` as "drop the memo table", so the next build is an
  ordinary first build.
- **WITNESS:** `git:c407ab7:Effect4Test/Counterexamples/Semantics/Layers.lean`: after
  `close`, a build raises the count and takes a new handle but joins neither
  the memo table nor the live set. The `rebuildAfterClose` golden shows the
  rebuild answering a second handle and the second `close` answering the empty
  order.
- **CLASS:** missing terminal state.
- **FIXED-BY:** a closed scope forks closed (`internal/effect.ts`,
  `scopeForkUnsafe`), so the construction lands in an already-closed layer
  scope and is released inside its own build. The handler carries `closed`.

## E4-SEM-CE-019 — what a layer trace does not say

- **BROKE:** reading the agreement of `generated/traces/layer/` as evidence
  about observer counting, concurrent builds, or layer composition.
- **WITNESS:** none for any of the three, and that is the row. A memoized
  rebuild registers the memo entry's finalizer a second time; at close that
  finalizer decrements `entry.observers` and releases nothing, so one release
  per *construction* reaches the wire and never one per build. `memoMapBuild`
  installs the entry and a `Deferred` before the construction runs, so a
  second fiber awaits the first fiber's result instead of constructing, and
  this handler is a single-fiber state machine over a single-fiber corpus.
  `Layer.provide` and `Layer.merge` need a layer *value* on the wire, and a
  layer is a build function, not a handle.
- **CLASS:** claim scope.
- **FIXED-BY:** the row is registered as a refusal;
  `git:c407ab7:Effect4/Layer/LayerFamily.lean` records all three in its module comment,
  `docs/research/TRACE-DAG.md` lists them among the things agreement does not
  establish, and the battery pins only what is claimed: two builds, one live
  entry, one release, and a four-operation surface.

