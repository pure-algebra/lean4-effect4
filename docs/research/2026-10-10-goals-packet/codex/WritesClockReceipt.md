# Exact Atomic writes and clock interference

The generic request-prefix helper needs a clock-free source premise.
The original Routing statement remains unchanged and its source discharges that premise.

## Placement

Atomic writes serve `Atomic.Store.shop_stages`, under store-typing and R4.
Their terms are the actual families checked by `shop_census`.
The proofs quantify over environments, store cells, counts and complete deposit histories.
Admission updates and returns the same branch.
Deposit appends its identity and returns the new balance.
Refill retains both outcome counts.
Cleanup records the count captured by its preceding read.
Each exact native step retains the other store fields.
These laws establish neither source uniqueness nor the whole shop history.

Clock interference bounds `recorded-call-tree-prefix`, under translation-simulation and R6.
`E4-HOST-CE-010` checks a clock read followed by an external call.
Both previous fragment tests admit it.
After an outside advance, the native request contains 17; the reply-only tree waits with 0.
`NoClockRead` rejects the control and accepts every actual Routing request.
The internal goal gains that premise; the original application statement does not change.
No owner ruling is required for this repair of our internal decomposition.
The original application statements remain the owner's contract.

## Integration

Base: `157107b4b`.
The roots connect full source history, complete frame sequencing and complete timeout native evaluation.
No runtime definition changes.
The original Timeout and whole-history custody clauses remain open.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.Writes Test.Dogfood.Scenario.Routing Test.Counterexamples.Machine.Runtime.HostClockPrefix Test.Dogfood.Proofs.HostTimeoutEvaluation Effect4.Laws.Program.ReleaseCustody.Execution Effect4.Laws`.
Result: success, 1323 jobs; `WritesClockBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/WritesClockAudit.lean`.
Result: success; `WritesClockAudit.out` retains the exact remaining goal.
The Atomic and Routing audit covers 141 declarations within `[propext, Quot.sound]`, five modulo declarations and one planned goal.
The evaluator, frame sequencing and reply source audit covers 573 declarations within the same ceiling, with no planned dependencies.

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.SourceUse Effect4.Laws.Program.NativeReplies`.
Result: success, 1089 jobs; `SourceHistoryIntegrationBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/RegistrationSourceAudit.lean`.
Result: `SourceHistoryIntegrationAudit.out` retains the independent integrated source and heap audit.

## Remaining work

Routing's actual native request-position proof remains open under the repaired fragment.
Atomic's stages require source use and environment aliases beyond these store equations.
Custody needs command ownership and parked-frame correlation through whole histories.
Timeout needs returned-value provenance through commands, then retry and cleanup history.
The final generated proof-graph refresh remains due.
The previous behavior-gate receipt retains its scope; this landing changes no runtime semantics.
