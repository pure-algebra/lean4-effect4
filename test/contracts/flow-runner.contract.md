# Contract: the Flow runner and the decision tape (P-T2)

Light ceremony by operator ruling D2 (`~/.claude/plans/misty-frolicking-naur.md`):
contract, battery and code land together. Effects pin: v0.4.0 (`e86f141`,
Flow v2).

## Frozen surface

| Name | Module | Shape |
| --- | --- | --- |
| `Effect4.Flow.Decision`, `Tape`, `TapeRead`, `Tape.read`, `Tape.wire` | `Effect4/Flow/Decision.lean` | the choice tape, consumed by occurrence with a site check |
| `Effect4.Frontier` | `Effect4/Semantics/Frontier.lean` | `fuel (block)`, `unansweredDecision (site)`, `stuck (block)` |
| `Effect4.Flow.RunResult` | `Effect4/Semantics/Runs.lean` | `done (value)`, `frontier (reason)`, `refused (expected actual)` |
| `Effect4.Flow.FlowService` | `Runs.lean` | `handle : Op → Val → M Val`, `pure : Op → Bool` |
| `Effect4.Flow.plan`, `Plan`, `step`, `Next`, `loop` | `Runs.lean` | pure control, effectful step, fuelled loop |
| `Effect4.Flow.run`, `runTape`, `runDefault`, `fuelFor` | `Runs.lean` | run from the entry with `[input]`; `fuelFor raw tape = (tape.length + 1) * blocks.length + 1` |
| `Effect4.Target.EffectV4.tableAlphabet`, `OpSpec`, `OpKind`, `tableService`, `tableNameOf`, `Script.toFlow`, `AtomTable` | `Effect4/Target/TypeScript/ScriptFlow.lean` | the embedded alphabet and the straight-line embedding |

## Laws (each one induction or none)

| Theorem | Statement |
| --- | --- |
| `Tape.read_answered_length` | an answered read consumed exactly one entry |
| `step_choose_consumes_one` | a `choose` at the head site logs `decide` and continues with the tail |
| `plan_checked` | on a well-formed flow, a block with a well-sized environment never plans `stuck`, and every continuation resolves to a block of the environment's size |
| `step_checked`, `loop_checked_not_stuck`, `run_checked_not_stuck` | over `StateT σ Id`, a checked run never reports `stuck` |
| `loop_fuel_mono`, `run_fuel_mono` | more fuel changes nothing about a run that did not exhaust its fuel |

Axiom receipts: `Effect4Test/Flow/RunnerAxiomReport.lean`, within `propext` and `Quot.sound`.

## Semantics pinned

- Fuel exhaustion is `frontier (fuel block)` with a trailing `frontier` event, never a
  `done` outcome (DB-04; row `E4-FLOW-CE-017`).
- Tape exhaustion is `frontier (unansweredDecision site)` with a trailing `frontier`.
- A tape entry for another site is `refused expected actual` with no `decide` event
  (ruling R6; row `E4-FLOW-CE-018`).
- Pure operations (`FlowService.pure`) run but log nothing; family operations log `op`
  and `answer`; a `ret` logs `done (success value)`.
- The internal oracle: for every program with a flow golden, the runner's log agrees
  with the traced service's log under `m2` (`harness/trace/Generate.lean oracle`,
  part of `scripts/check-trace-goldens.sh`); goldens under `generated/traces/flow/`.

## Acceptance

```text
lake env lean Effect4Test/Flow/RunnerContract.lean
lake env lean Effect4Test/Counterexamples/Flow/Runner.lean
lake env lean Effect4Test/Flow/RunnerAxiomReport.lean
./scripts/check-trace-goldens.sh
./scripts/test-trace-goldens-gate.sh     # 4/4 planted defects
./scripts/test-trust-gate.sh
```
