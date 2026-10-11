# Atomic cleanup source dependency

Apply `atomic-cleanup-source.patch` with `git apply --unidiff-zero` at the coordinator tree.
The baseline file hash is `01755c26e330de896a95e48a83872e895d0aaca3`.
The file is `Test/Dogfood/Scenario/Atomic/Cleanup.lean`.

- Base: `a7a1d456`.
- Proof role: preservation.
- Evidence status: proved modulo the existing cleanup-log writer goal.
- Concept: scope-lifetime-finalization, R11.
- Consumer: original `Atomic.cleans_once` through `Cleanup.cleaned`.

The original cleanup reader consumes actual six-path registration uniqueness.
It no longer depends on the broader `FinalizerRun.once_placed_pushes_once` goal.
The selector equality connects the existing finalizer classifier to the checked application count.
The original statement and cleanup-log writer obligation remain unchanged.

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.Cleanup` succeeds with 1099 targets.
The cleanup module takes 2.2 seconds.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicCleanupSourceAudit.lean` succeeds.
It audits nine declarations within `[propext, Quot.sound]`.
One declaration remains modulo the single existing `Cleanup.log_debits` planned goal.
No whole cleanup-log proof or new runtime evidence is claimed.
