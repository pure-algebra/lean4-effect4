# Actual host reply facts

The routing call-prefix goal remains open; the new facts follow actual session admission and actual source ownership.

## Placement

Concept: translation-simulation, R6. Consumer: `Run.CallTree.request_leads`, then the original Routing authorization statement.
`SourceScope.NameAt` retains the authored call address of each external registration.
Existing compilation and command proofs supply that address without a second source carrier.
`HostReplyTape` proves that checked call instances retain closed table reply columns.
Both admission branches pass the local reply check at the current allocation table.
External-only histories retain source ownership and exclude delayed reference reads.
A live external request therefore names an actual source call.
These facts establish neither the whole call-prefix simulation nor agreement at a different allocation table.
They establish no progress or outside-host result.

## Landing

Base: `8d9596ba1`.
Changed files: `Laws/Program/NativeScope.lean`, new `Laws/Program/HostReplyTape.lean`, and `Laws/Run/CallTree.lean` under `src/Effect4/`.
The CallTree import connects the helper module to its named consumer and the law root.
No scenario statement changes.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.HostReplyTape Test.Dogfood.Scenario.Routing`.
Result: successful, 1104 jobs; `HostReplyTapeBuild.log` retains the output.
Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/HostReplyTapeAudit.lean`.
Result: 433 declarations within `[propext, Quot.sound]`, with zero goals and zero planned dependencies in the audited modules.
The status output explicitly retains `request_leads` as open.
`HostReplyTapeAudit.out` retains both results.
No runtime definition changes; no behavior gate is newly reached.
The final proof graph refresh remains due.
