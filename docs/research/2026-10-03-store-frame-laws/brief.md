# Store frame laws, slice C

Base: `8913519b146d95c07a3eaa195df1a1fcda2c642a`.
Branch: `codex/store-frame-laws`.
Owner: Codex store-frame seat. Coordinator owns integration and root imports.

## Settled contract

For every `SyncOp`, stores `s` and `s'`, and answer `v`,
`syncOpStep o s = some (s', v)` implies `s'.externals = s.externals`.
There is no validity, well-formedness, empty-allocation, source-typing or row-table premise.
The equality covers queued answers, allocated labels and the rejected-answer marker.
It concerns successful synchronous store primitives only. Their existing `none` results
remain unchanged. No runtime definition, invariant or existing obligation is weakened.

The current `#frame_rules` generator already supplies one-field record-update rules.
No new field alphabet, footprint catalogue or frame generator is needed for this consumer.
The missing information is the operation-wide equality of the untouched external store.

First consumer: `Sched.storesOk_syncOpStep` in `Simulation/Hooks.lean` establishes its
external-allocation clause once using this law. Its registration-key reasoning stays on the
current branches and keeps the existing theorem and `M1Hooks` obligation types unchanged.
This removes repeated reconstruction of the independent external-allocation clause from
scope and memo branches. It does not collapse the coupled scope/name-supply invariant.

After that migration passes, inspect the existing typed-store helper for a second local
consumer: derive an external-store equality directly from its existing successful-step
premise rather than requesting callers supply it. Add a path to the fence only after
identifying the helper and its concrete callers; keep frozen obligation types unchanged.

## Proof placement before work

1. Concept 10, translation and simulation, serving `run-eq-ref` through the existing
   `M1Hooks.storesOk_syncOpStep` obligation. The store-invariant clause is the no-external-
   allocation fact consumed by `replay_externals` and the recorded-result connector.
2. Local goal `Machine.StoreFrameWanted.syncOpStep_externals`, before its proof. Its
   immediate consumer is `Sched.storesOk_syncOpStep`; any helper has that same consumer.
3. Reach: exact equality of `ExternalStore` for any successful `syncOpStep`. The consuming
   frame/reference agreement still has its empty-table/default-oracle boundary (DI-57,
   decision 138). Host-session admission remains a separate obligation (rows 95, 97-99).
4. Not established: operation commutation; absence of reads; preservation of other fields;
   arbitrary callback or host-answer behavior; progress or liveness; validity of returned
   handles; machine/host equivalence; a target storage or compiler correctness result.
5. Unlocks: stable operation facts for R8's runtime correspondence and R13's proof-facing
   APIs. M5-M7 are existing dependencies, not obligations reopened by this slice. A later
   storage backing may consume this equality but still owes its own relation and lifting.

## Edit fence and checks

Allowed:
- `src/Effect4/Laws/Machine/StoresLaws.lean`
- `src/Effect4/Laws/Program/Simulation/Hooks.lean`
- `Test/Machine/Runtime/StoresLawsContract.lean`
- `src/Effect4/Laws/Program/Typed/Commands/Clauses/StoreScope.lean`
- this brief, receipt and evidence in `docs/research/2026-10-03-store-frame-laws/`

No root imports, generated output, runtime definitions, dirty main documents, decision
register, or coordinator-owned Denote/Agreement/MeaningEq files change.

Acceptance: narrow builds for StoresLaws, Hooks and their direct dependents; existing
StoresLaws contract with exact type pin and axiom check; concrete nonempty external state
with all three fields populated, successful operations that change different store families,
and an absent-operation frontier. Preserve the existing scope-key counterexample controls.
Run `#auto_census` before any bank-based rewrite and use the existing Stores bank only if it
removes proof work at a named consumer. One Lean build process at a time in this worktree.
No full sweep, no push. Commit named paths only after verification and receipt.

## Second consumer, settled after the primitive law passed

`Evaluating.store_restate` already takes the successful sync step. It unnecessarily asks
for external-store equality separately; all eight callers, in the same StoreScope module,
supply `rfl`. Derive that equality from `syncOpStep_externals` inside the helper and remove
those eight arguments. This strengthens only the helper by removing a redundant premise.
Every public `StoreClauseKeeps` statement and ledger obligation stays unchanged. Placement:
concept 4, the existing store-clause route to M6 and `step-deliver-preserves`/
`step-loop-preserves`; the concrete consumers are scopeMake, open scopeAdd, scopeRemove,
scopeFork, memoFork, memoGet hit, and both memoRelease branches. The existing coupled
world, scope and memo proofs are retained.
