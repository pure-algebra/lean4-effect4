# Queue proof seat receipt

The unrestricted job ledger claim has a checked counterexample.
The public conservation claim now requires terminal external replies.
The cleanup history and command preservation goals remain open.

The base is `5f07927c8`.
The branch is `codex/meanings-queue` in `/private/tmp/meanings-queue`.

## Placement and scope

The source and acquired-answer laws serve store-typing R4 and scope-lifetime-finalization R11.
Their consumers are `QueueWorkers.Assertions.logs_history` and the Workers cleanup history claim.
They retain source positions, initialized leading bindings, and acquired literal identities.
They establish local compilation and callback facts, without an initialized command history invariant.

The reply control serves translation-simulation R10 and `QueueWorkers.Assertions.jobs_step`.
`QueueWorkers.RefReplyControl.refutes` uses an actual admitted, funded six-move session with two jobs.
The session accepts a delayed read from the count reference.
Its original fed observation is empty, while its held observation contains job zero.
The control uses kernel reduction and retains `Assertions.RawJobs` as the original false assertion.

`TerminalReplies` narrows the admitted input profile.
It does not repair general-admission accounting.
The public `HeldWithinFed` statement exposes this premise.
A checked terminal-reply journal supplies the premise through `Assertions.terminal_of_check`.
All existing named scenario and control runs pass `terminalRepliesCheck` in the finite normal-profile probe.
This finite check establishes no conservation theorem.

## Commits and checks

Every Lean command uses `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.

| Commit | Content | Checked evidence |
| --- | --- | --- |
| `83e96e62e` | Prefix source graph and callbacks | Narrow build; audit 540 declarations, zero goals and zero dependencies on goals. |
| `9cebd5483` | Interpreter and action prefix transport | Narrow build; audit 135 declarations, zero goals and zero dependencies on goals. |
| `6d7c5f126` | Terminal reply premise and actual-history counterexample | Queue build; current control audit seven declarations, zero goals and zero dependencies on goals. |
| `4a5d1e525` | Protected typed graph, compilation, acquisition and concrete queue source laws | `lake build Effect4.Laws.Program.AnswerSlots.TypedAcquisition`: 398 jobs; audits 437 and 85 declarations, zero goals and zero dependencies on goals. |
| `618ad2287` | Acquisition body, stored captures, source callback points and queue specification | `lake build Effect4.Laws.Program.AnswerSlots.TypedPoints`: 400 jobs; `lake build Test.Dogfood.Proofs.QueueWorkersFlow`: 1287 jobs; audit 43 declarations, zero goals and zero dependencies on goals. |

All reported audits admit only `propext` and `Quot.sound`.
The source changes do not alter Machine, Eff, Ty or Store.Val.
No shared root, registry, decisions file or lakefile changes in this seat.

## Remaining obligations

The stable graph still needs complete native evaluation and the initialized machine connection.
The coordinator owns the joint guarded machine, queue and task driver.
This seat owns the reusable initializer and stable answer model.
`logs_history`, `jobs_step` and `rest_step` remain planned goals.
No behaviour comparison establishes those unfinished proofs.

## Native answer extension

`d57a8c5d5` adds actual synchronous allocation answers and whole continuation return wrappers.
Ready workers use a broad yield class that allows other workers to grow deferred stores.
Transient initialization yields retain exact lengths and require the initialization phase.
The explicit readiness decision avoids `Classical.choice`.

The narrow command is `lake build Effect4.Laws.Program.AnswerSlots.InitializedSync Effect4.Laws.Machine.AnswerFlowResume Test.Dogfood.Proofs.QueueWorkersLogValues Test.Dogfood.Scenario.QueueWorkers.RefReplyControl`.
It passes 1327 jobs before the readiness decision repair.
The repaired dependency build checks the changed initialized modules again.
`lake env lean InitialAudit.lean` audits 204 declarations without goals or dependencies on goals.

The concrete log-value extension reads actual source updates and their protected environment.
`QueueWorkersLogValues.operation_value` proves the actual cleanup update appends its acquired identity.
Its premise is the typed source-operation certificate, which the history producer must establish.
`lake build Test.Dogfood.Proofs.QueueWorkersLogValues` passes 1303 jobs.
`lake env lean QueueAudit.lean` audits 254 declarations without goals or dependencies on goals.
Both audits admit only `propext` and `Quot.sound`.

The Overwatch suggestion to read values from `resumedWith` does not apply as stated.
That event records an unexecuted program, including delayed reference reads.
`RefReplyControl.resumed_delayed` retains this fact by kernel reduction on the admitted control.
The current terminal-reply correction remains explicit.
A general-admission fed observation still needs an actual continuation-value witness.
No machine or trace definition changes.

The unrestricted native history producer remains open.
The bare root-cell producer for Atomic and Timeout also remains open.
The current initialized model requires a crew gate and protected acquisition specification.
It does not establish a standalone root-cell history for those other programs.
