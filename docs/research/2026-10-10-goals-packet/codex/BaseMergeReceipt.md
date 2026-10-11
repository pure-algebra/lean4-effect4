# Shared machine laws integration

The seven shared machine laws now include the goals branch's first-exit race action.
No scenario goal closes in this integration.

Base: `fb4593bbd`. Incoming base: `5376985e3` on `refactor/phase1-phase3`.
Head: the merge commit containing this receipt.

The merge retains both counterexample register appendices.
`Moves`, `Footprint`, `Interference`, and `StackLocal` each gain the `raceAllFirst` case.
The case follows `evaluatePrim.withFiber` in `src/Effect4/Machine/Fibers.lean` through `beginRace` with `.firstExit`.
The remaining incoming files retain their base contents.

## Verification

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Counterexamples.Program.ContextReset Test.Counterexamples.Codegen.PrintDistributes Test.Dogfood.Scenario.Workers`: passed, 1353 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/BaseMergeAudit.lean`: passed.
- The audit reports 729 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
- `git diff --check`: passed for the four unstaged integration edits.
- `git diff --check --cached`: reports retained whitespace in four incoming research files.
  These files are `coherence.lean`, `families-probe.lean`, `section7.lean`, and `modgraph.py`.
  The merge preserves their existing evidence bytes.

The logs are `BaseMergeBuild.log` and `BaseMergeAudit.out` beside this receipt.
These are proof checks. They make no new host observation claim.
The behavior gates remain scheduled after the next major proof structure.
The guard cleanup, live command classification, run stack locality, and source topology remain open.
The services chain waits for the owner's context ruling.
