# Timeout R2 adapters

The numeric family builds; the original Timeout endpoint still requires message settlement transport.

Base: host checkpoint `125865d206dfedd3434d460010366f4fd136d84b` with coordinator R2 dependency snapshots.

Changed modules: `HostTimeoutEvaluation`, `HostTimeoutNumberEntry`, `HostTimeoutNumberCallbacks`, and `HostTimeoutNumberFlow`.
All four live under `Test/Dogfood/Proofs/`.

The exact iteration equations include the new empty message list.
The internal await reader uses the canonical countdown plan.
The public eager countdown theorem retains its original statement.
The proofs establish the same local callback and frame claims.
They establish no numeric reached-history producer.

Verification: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Effect4.Laws.Program.HeapSites` passes, 1,138 jobs.
The log is `/private/tmp/store-transfer-numeric-r2-build.log`.

Audit: `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/timeout-r2-adapters-audit.lean` passes.
It audits 294 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations resting on goals.
The log is `/private/tmp/timeout-r2-adapters-audit.log`.

`Scenario.Timeout` reaches an old eager countdown proof in `HostTimeoutParkSteps` and fails.
The original source-value history requires the new addressed-message transport before its next check.
The original `retries_declared` and `cleanup_keeps` goals remain open.
No executable file belongs to this adapter patch.
No behavior gate applies to these proof-only edits.
