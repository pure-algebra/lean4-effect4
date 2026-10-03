# Store frame laws receipt

Merge note: this slice changes proof APIs only. The full external-store equality has no
validity or empty-store premise. It removes a redundant argument from `store_restate`;
all eight callers are migrated, and the direct consumers compile. No coordinator-owned
file, runtime definition, existing invariant or frozen ledger statement changed.

Base: `8913519b146d95c07a3eaa195df1a1fcda2c642a`.
Implementation head: `e5ec94dec2a16339d254204c5dc9acab24dad97c`.
Branch: `codex/store-frame-laws`. No push.

## Result and actual consumers

`Machine.syncOpStep_externals` proves that every successful synchronous store operation
leaves the entire external store unchanged: queued answers, allocated labels and the
rejected-answer marker. The theorem has only the successful-step premise. The local
`StoreFrameWanted` ledger reports `0 open, 1 proved, 1 total; ceiling 0`.

`Sched.storesOk_syncOpStep` now proves its external clause once before the operation cases.
The explicit external-clause references fall from seven to one. The coupled scope-key/name-
supply reasoning and theorem statement are unchanged. The existing `#frame_rules`
mechanism remains in place; no second frame generator or field catalogue was added.

`Typed.Evaluating.store_restate` derives its external-store equality from its existing
successful-step premise. Eight typed scope/memo callers no longer pass that argument.
Their world, scope, memo, value-membership and postcondition premises stay intact. Every
public `StoreClauseKeeps` statement and obligation remains unchanged.

## Proof placement

1. Concept 10, translation and simulation: the new exact external-store frame supports
   `run-eq-ref` through `Sched.M1Hooks.storesOk_syncOpStep`. Concept 4, reactive scheduling,
   gains the typed-store helper consumer on the existing M6 route to
   `step-deliver-preserves` and `step-loop-preserves`.
2. Question: `Machine.StoreFrameWanted.syncOpStep_externals`, stated before proof and
   linked with `#obligation_proved`. Its concrete consumers are the simulation invariant
   and `Evaluating.store_restate`; the latter serves scopeMake, open scopeAdd, scopeRemove,
   scopeFork, memoFork, memoGet hit and both successful memoRelease branches.
3. Reach: arbitrary `SyncOp`, stores and answer, conditioned only on
   `syncOpStep o s = some (s', v)`. This is exact `ExternalStore` equality. The consuming
   reference simulation retains its empty-table/default-oracle boundary (DI-57, decision
   138); host admission remains separate (decisions 95, 97-99).
4. Not established: step existence, progress, liveness, operation commutation, absence of
   reads, preservation of other fields, host-answer safety, target storage correctness or
   any host/compiler equivalence. Cross-table Fits and memo invariants are not collapsed.
5. Serves R8 and R13 with a stable proof-facing operation fact and removes caller work on
   the M6 spine. It introduces no new general scheduler or host guarantee.

## Verification

All commands and selected stage output are in `evidence/verification.txt`; the exact axiom
query source and full output are in `evidence/axioms.lean` and `evidence/axioms.txt`.
The narrow source builds, direct-consumer build, stores contract and simulation contract
passed. The downstream existing ledgers report M6 `20/20` and M7 `4/4` proved.

The stores fixture pins the theorem at its exact type. Eight new guards include six
successful-step checks with all three external fields populated, a check that another
store field actually changes, and the existing absent-reference result remaining `none`.
The positive guards check `Option.map ... = some externalFrame`, so an absent result
cannot make them pass. These are finite execution checks; the theorem is universal.
Existing scope-key counterexample controls remain in the passing simulation contract.

Axiom queries for the new law, both migrated helpers and seven typed clause theorems all
report exactly `[propext, Quot.sound]`. `git diff --check` passed. No full test/trust sweep,
code generation, host runtime or target compiler test was run or is claimed. The first
proof attempt needed `syncOpStep` added to the named aesop normalization facts; the theorem
statement was unchanged. Coordinator source review found no substantive concern.

## Changed source paths

- `src/Effect4/Laws/Machine/StoresLaws.lean`
- `src/Effect4/Laws/Program/Simulation/Hooks.lean`
- `src/Effect4/Laws/Program/Typed/Commands/Clauses/StoreScope.lean`
- `Test/Machine/Runtime/StoresLawsContract.lean`

No new root imports or decisions row is needed. This slice closes its local obligation;
remaining host and lowering obligations stay open under their existing owners.
