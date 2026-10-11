# Queue command-boundary assertions receipt

The four original clauses compile modulo three named preservation goals.
The job count remains universal, and all original clause premises remain.

## Placement

- Concept: translation-simulation, R10, proposed `queue-expansion-agrees` and `waiting-request-obligation-preserved`.
- Concept: reactive-scheduling, R12, proposed `wait-registration-no-gap` and `waiting-request-obligation-preserved`.
- Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
- Consumers: `QueueWorkers.held_within_fed`, `fed_accounted`, `queue_settled` and `releases_once`, assembled by `queueWorkers`.
- Reach: the actual built crew, every total, every command budget, raw rows and session-admitted replies.
- Rest premises: the original host-act script and `atRest` premises.
- Limits: no progress, fairness, release order or outside-host behavior claim.

## Landing

Base: `13b29da88`, with shared Frame and ReleaseTrace dependencies.
The landing commit contains this receipt.

Changed files:

- `src/Effect4/Laws/Library/Queue/Conservation.lean`
- `Test/Dogfood/Scenario/QueueWorkers.lean`
- `Test/Dogfood/Scenario/QueueWorkers/Model.lean`
- `Test/Dogfood/Scenario/QueueWorkers/Ledger.lean`
- `Test/Dogfood/Scenario/QueueWorkers/Assertions.lean`
- `docs/research/2026-10-10-goals-packet/codex/QueueAssertions.lean`
- This receipt.

The model extraction retains the names and exact bytes of 28 definitions.
The four original goal declarations retain their exact bytes.
The moved definitions have SHA256 `996c1f004dd268fb055dfe237041069864154dc055577dae68c463721c6a0b6c`.

The shared model laws account for take, offer, poll and both withdrawals.
They establish no machine-to-model connection.
The ledger port retains the packet's proved observation readings and refused-row facts.
The new assertions state conservation and cleanup at every funded command boundary.
They retain custody, loss, admitted history, source placement and concrete trace/store debit counts.
The rest assertion relates actual queue wait counts to idle crew members.
The script lifts consume proved refused-row conservation and cleanup leaves.

## Checked commands

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.QueueWorkers.Assertions Test.Dogfood.Scenario.QueueWorkers` succeeds.
The original scenario rebuild takes 33 seconds, as reported by Lake.

The final assertion build uses `/usr/bin/time -p env LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.QueueWorkers.Assertions`.
It succeeds with 1045 jobs; real 2.48 seconds, user 0.91 seconds, sys 1.13 seconds.

The final probe uses `/usr/bin/time -p env LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/QueueAssertions.lean`.
It succeeds; real 2.87 seconds, user 1.81 seconds, sys 1.02 seconds.

Audit output:

```text
#axiom_audit: 349 declarations within [propext, Quot.sound], 9 of them modulo planned goals; 3 planned goals
```

The proof-plan output reports these exact remaining dependencies:

| Assembly | Goals |
| --- | --- |
| `Assertions.held_within_fed` | `Assertions.jobs_step` |
| `Assertions.fed_accounted` | `Assertions.jobs_step`, `Assertions.rest_step` |
| `Assertions.queue_settled` | `Assertions.jobs_step`, `Assertions.rest_step` |
| `Assertions.releases_once` | `Assertions.cleanup_step` |

`git diff --check` succeeds.
The extraction check compares each moved declaration against `b67e9b9c` and succeeds.
Disk availability measures 20 GiB after the narrow builds.

## Open obligations

`jobs_step` needs the queue-cell writer census, admitted take replies and once-entered continuations.
`rest_step` needs committed custody, interrupted withdrawal and queue wake-to-wait correspondence.
`cleanup_step` needs control-source provenance, registered closure ownership and cleanup-cell writer provenance.
The assemblies are proved modulo these goals; no original scenario clause becomes proved outright.

The coordinator replaces each original goal body with its matching `Assertions` theorem.
The coordinator imports the shared conservation module through the Laws root.
The coordinator imports Assertions through the scenario or Test root.
Root imports and the original four goal bodies remain outside this lane's edits.
No full check gate, outside-runtime comparison or push runs in this lane.
The program and observation definitions remain unchanged, so this landing introduces no behavior change.
