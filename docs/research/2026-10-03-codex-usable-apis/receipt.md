# Slice A receipt: journaled controls and replay

The integration fact to retain: this is conditional equality of the resulting **machine**.
Every newly added control row must have progressed. It does not identify session metadata,
prove host-answer admission, or claim equality after a refused or fuel-limited step.

Base: `6366de3b5f4d467724f9d359551c7ef14c6c25c5`.
Implementation head: `8f1494d7c0a973431fb3a75203ed2fe8ec221eeb`.
Branch: `codex/run-replay-api`. Implemented in the isolated managed worktree
`/Users/pooks/.codex/worktrees/run-replay-api/lean4-effect4`.
User authorized the combined plan and first ready implementation slice. No push was made.

The implementation was fast-forwarded onto `refactor/phase1-phase3`. Content hashes before
and after integration confirmed that all five pre-existing modified documentation files
were byte-identical: `docs/STATE.md`, `docs/core/architecture-map.html`,
`docs/core/semantics.md`, `generated/semantics.json`, and `generated/semantics.md`.
This receipt is a following documentation-only commit.

## What landed

- `src/Effect4/Laws/Run.lean`: a general connection from journaled control rows to raw frame
  replay; the existing ordinary-run theorem becomes its corollary with an unchanged
  statement; a new clock-run corollary uses the same connection.
- `Test/Run/RunContract.lean`: empty suffix, ordinary and clock-driven host waits at a
  nonempty table, a sleeping child awaited by its parent, distinct compile/command budgets,
  previously refused history followed by progressing controls, and a negative fuel case.
- `plan.md`: the combined consumer-led slice plan, incorporating Claude's T-LOW work and
  the source/probe corrections to the handler, editing, store and scheduler proposals.
- `Probe.lean`: eleven finite planning assertions. Equal local layer types can still leave
  a dangling reference; operations with disjoint writes can still return different answers
  when reordered. These are concrete discriminators, not universal theorems.
- `Axioms.lean`: reproducible exported-statement and transitive axiom inspection.

No runtime definitions, source syntax, checker rules, root imports, generated files or
coordinator authorities changed. The source edit fence was exactly the two named Lean files.

## Placement and exact reach

The [plan](plan.md) recorded the five required placement items before proof work. The local
`ControlReplayWanted.play_controls_eq_replay` obligation also precedes its proof in source.

| Declaration | Placement and consumer |
| --- | --- |
| `ControlReplayWanted.play_controls_eq_replay` | Concept 10, Translation and Simulation, with concept 9's session protocol as the executable boundary; the concrete local ledger goal for proposed claim `run-controls-replay` |
| `play_phases_extend` | Helper for that goal; establishes that playback appends phases, allowing cancellation of earlier history |
| `play_controls_eq_replay` | Proves that goal; consumed immediately by ordinary and clock-run connectors |
| `runPure_eq_run` | Existing O-10 connection, unchanged statement, now derived through the general theorem |
| `runClock_eq_run` | Clock-driven consumer of the same connection, with arbitrary adjustment lists |

The general statement is:

```lean
(s.play (Rows.tape tape)).phases =
  s.phases ++ List.replicate tape.length Phase.progressed
  → (s.play (Rows.tape tape)).machine =
      machineOf (replayFrom s.built.program s.built.table s.budget.fuel tape s.machine)
```

It starts at the existing Run's machine, not a reloaded program. It uses the same supplied
row table, command fuel and decision list. Earlier phases may include applied answers,
refusals or frontiers. The ordinary and clock-run corollaries explicitly retain the separate
compile budget and give raw replay an empty answer list. There is no Straight/Looped syntax
restriction; the premise limits the executions being compared, not the program fragment.

This serves R8's named face connections and R13's recorded-run inputs. Downstream typing
results may consume the connection under their own premises; the proof does not depend on
M5-M7. The onward reference-machine connector still has its empty-table boundary (decision
138, DI-57). Host admission remains at decisions 95 and 97-99. No decisions row is amended.

Proposed theory/registry entry for the coordinator: concept 10 required property
“journaled controls agree with frame replay on the same starting machine, table, budgets
and tape whenever the added phases all progress”; claim `run-controls-replay`, role
`simulation`, declaration `Effect4.Run.play_controls_eq_replay`. This is proposed here
rather than changing the owner's dirty semantics and generated registry documents.

Open beyond this slice: equality on frontiers or refusals, session metadata correspondence,
unconditional progress, termination, fairness, runtime host-answer admission, table-aware
frame/reference agreement, source-transformation correctness and target execution. The fuel
fixture demonstrates that dropping the phase premise is false for machine equality:
journal playback executes a later middleware command while raw replay stops at the earlier
fuel frontier. It is not advertised as a counterexample for the narrower named `Obs`.

## Verification

All commands ran in the isolated worktree above using Lean 4.33.1, serially. Final results:

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Run` | Passed, 317 jobs; control-replay ledger: 0 open, 1 proved, 1 total |
| `lake build Test.Run.RunContract` | Passed, 332 jobs, including the exported axiom guards |
| `lake env lean docs/research/2026-10-03-codex-usable-apis/Probe.lean` | Passed, all eleven finite assertions, no diagnostics |
| `lake env lean docs/research/2026-10-03-codex-usable-apis/Axioms.lean` | Passed; exact statements inspected and outputs below |
| `git diff --check` and `git diff --cached --check` | Passed |

Every declaration printed by `Axioms.lean` reports exactly `[propext, Quot.sound]`:

```text
Effect4.Run.ControlReplayWanted.play_controls_eq_replay
Effect4.Run.play_phases_extend
Effect4.Run.play_controls_eq_replay
Effect4.Run.runPure_eq_run
Effect4.Run.runClock_eq_run
```

Initial attempts exposed list-reduction proof errors and fixture constructor spelling
errors; these were repaired without weakening the theorem statement or dropping a fixture.
The final saved probe and axiom files were run again from their retained paths. An
independent source review found no substantive issue; its wording correction about the
negative test's machine field was applied before the passing test build.

No full battery, global axiom-gate sweep, `make check`, or target runtime test was run.
This was the repository's narrow slice validation, not a coverage sweep. The first next
implementation is slice B's general path replacement with the existing layer-editing
consumer; broader typed editing and service execution keep the contracts in the plan.
