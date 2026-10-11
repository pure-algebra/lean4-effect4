# Actual writer integration

The actual Timeout and Atomic writer proofs compile together.
Their history-level permissions and ordering remain open.

Base: `7366b729f`.
Integrated source commits: `cac397fd3`, `d0f636d05`, `f59f6b420`.
Root commits: `1f27a097d`, `c657e0afc`, `82b6c97f2`.
The enclosing commit adds the two new Test imports and this receipt.

## Scope

Timeout source positions retain a four-attempt index and declared retry evidence after a caught failure.
The numeric source leaves describe the actual reference operations and exact cleanup and completed-exit readers.
The actual run still must connect the heap count to the source index and preserve interruption ordering.

Atomic writer leaves describe all six actual cleanup-note sites and their store effects.
The run still must issue a single write permission at each actual finalizer start and consume it at the note.
The Workers checkpoint remains a compiled research probe with its source and heap premises explicit.
No original goal changes its statement or closes through these source leaves alone.

## Commands and results

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Timeout Test.Dogfood.Proofs.HostTimeoutNumberLedger Test.Dogfood.Scenario.Atomic.Writer`

The narrow build passes with 1158 jobs; see `WriterIntegrationBuild.log` beside this receipt.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/WriterIntegrationAudit.lean`

The audit checks 513 declarations within `[propext, Quot.sound]`, with zero goals or declarations modulo goals.
The original `stale_never_applies` remains proved.
The original `retries_declared` and `cleanup_keeps` remain planned goals.
See `WriterIntegrationAudit.out` for the exact output.

These changes concern proofs and readers only.
The external behavior comparison remains the checked sweep in `history-behavior-sweep-receipt.md`.
No whole-tree battery or policy check runs.
