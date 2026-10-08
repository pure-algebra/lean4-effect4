# Final Pool step measurements

Pool's step battery passes against the checked fused conditional-map dependency.
No behavior, typing, reading, or refusal guard changes.

Dependency: checked `928402930822c07ff31719621d21ef1653e3dd9d`.
Owned battery: `Test/Program/PoolSteps.lean`.

The independent probe `docs/research/2026-10-08-seat-step-measure-probe.lean` measures the fused compiled dependency through a read-only path.
It reports lease as 167 nodes and five folds, and leasedOf as 28 nodes and one fold.
The interim composed version reports 198/seven and 59/three respectively.
The earlier raw version pins 166/seven and 29/two respectively.
Other updated pins are return 67/two, withdrawal 23/one, drain 61/three, headStamp 6/zero, marked 28/one, and withdrawn 21/one.

The fused helper removes the repeated filter subtree.
These are finite stored-term measurements, not a runtime cost law or a host measurement.

## Exact checks

`LEAN_NUM_THREADS=3 lake env sh -c 'LEAN_PATH="/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4/.lake/build/lib/lean:$LEAN_PATH" lean -DwarningAsError=true /private/tmp/module-step-measures.lean'` passes.
The dependency worktree HEAD is `928402930822c07ff31719621d21ef1653e3dd9d`.

The dependency artifact path lacks `Test.Program.QueueSteps`.
A first direct battery check refuses that missing object file.
The already checked QueueSteps object is copied into `/private/tmp/final-battery-deps/Test/Program/QueueSteps.olean`.
No source or artifact in the dependency worktree changes.

`LEAN_NUM_THREADS=3 lake env sh -c 'LEAN_PATH="/private/tmp/final-battery-deps:/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4/.lake/build/lib/lean:$LEAN_PATH" lean -DwarningAsError=true Test/Program/PoolSteps.lean'` passes.

Approval review refuses two cross-seat dependency cherry-picks before execution.
The permitted read-only compiled-dependency setup resolves that boundary.
The coordinator owns the final integrated build and axiom gate.
