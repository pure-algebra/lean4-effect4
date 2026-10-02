# CE-026 control battery

The general `wake_preserves` proof was already committed by Claude. This slice supplies its
missing positive and rejecting controls and marks CE-026 repaired; it changes no production
definition or proof target. The remaining M6 and M7 goals stay open.

Base: `247d74872a6b0437d25b5660e1450b580faf3bfb`. Branch: `codex/proofs-lead`.
Head: the commit containing this receipt. Files are `Test/Program/WaiterColumn.lean`,
the import immediately after `MemoTable` in `Test/All.lean`, CE-026's register row, this receipt
and `plan.md`. No push. The historical D3 probe is unchanged.

Placement and scope are in `plan.md`: reactive scheduling, `M6Ledger.step_wake`, decision 134(b),
with the store column from Concept 1. The fixture's helpers construct the actual former witness.
`natWorld_refused` rejects its wrong token type; `config_typed` proves that correcting that type
admits the same machine; `result_typed` applies the existing general theorem to its real wake.
The other six printed results check completed delivery, clearing the batch, uncompleted rejoin,
the deliberate ignored Deferred stamp, no duplicate delivery on a repeated wake, and a missing
cell. These are finite reference-machine equations, not host or target conformance.

## Verification

Lean is the project's pinned 4.33.1. The initial build-cache copies were checked before use:
397 source inputs match their saved Lake traces and 1,061 output artifacts match saved hashes
and their independent copies. Evidence: `/private/tmp/codex-lead-2026-10-02/base-provenance.json`.

Commands, run serially with `LEAN_NUM_THREADS=1` and process timeouts:

- `lake env lean -j1 -M2048 -DwarningAsError=true Test/Program/WaiterColumn.lean`: passed,
  3.33 seconds, 120-second bound. All nine printed declarations depend only on
  `[propext, Quot.sound]`.
- `lake build Test.Program.WaiterColumn`: passed, 3.63 seconds, 180-second bound; 404 jobs,
  dependencies replayed and the new test built. This is a narrow module build, not a whole-tree
  sweep. Saved logs: `waiter-attempt-2.log` and `waiter-build.log` in the same evidence directory.
- `git diff --check`: passed. The new battery is imported by `Test.All`.

The first attempt rejected an extra test assumption that a stale Deferred scheduling stamp was
inert. `Stores.wakeList` explicitly ignores that stamp because Deferred completion is inline;
the final controls test the actual contract and repeated delivery instead. The failed attempt
is retained as `waiter-attempt-1.log`, not counted as proof evidence. No production change was
made to fit that test.

No progress, fairness, arbitrary-host reply, whole-machine equivalence or generated-code theorem
is claimed. Generated proof reports await the handoff's integration checkpoint.
