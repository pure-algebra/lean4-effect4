# Actual request prefixes and proof integration

Routing authorization still depends on `CallTree.request_leads`.
The recorded-binding inversion and its call-tree observation are proved separately.

## Placement

Concept: translation-simulation, R6.
Question: `recorded-call-tree-prefix`, serving the original Routing authorization clause.
Reach: every recorded script and command budget, under `StraightRows` and `NoCauseHandler`.
`JournalPrefix.bound_request_prefix` recovers the actual preceding machine from an accepted binding.
`CallTree.tree_wait_of_leads` consumes existing local agreement to identify the tree wait.
`CallTree.request_leads` retains the unresolved native request-position obligation.
No original scenario statement changes.
The result establishes no progress, fairness or outside-host agreement.

`RoutingInterrupt.routing_interrupted` checks interruption on the actual Routing continuation.
Its premise requires an interruptible frame and a recorded interruption.
The mask control shows why that premise remains necessary.
This reader does not prove the complete source history.

## Integration

Base: `a1eee2177`.
`Test/All.lean` imports the checked timeout source, source-use and Routing interruption readers.
Release execution imports the checked continuation sequencing module.
The complete `Effect4.Laws` root builds with all landed proof branches.

## Checks

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Routing Test.Dogfood.Proofs.HostTimeoutNative Test.Dogfood.Scenario.SourceUse Effect4.Laws.Program.ReleaseCustody.Execution`.
Result: success, 1139 jobs; `PrefixIntegrationBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.RoutingInterrupt`.
Result: success, 1039 jobs; `RoutingInterruptBuild.log` retains the output.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/PrefixIntegrationAudit.lean`.
Result: success; `PrefixIntegrationAudit.out` retains the statements and audit.
The Routing branch has 103 declarations within `[propext, Quot.sound]`, five modulo declarations and one planned goal.
The timeout source, source-use and sequencing branch has 552 declarations within the same ceiling and no planned dependencies.
Routing infrastructure is proved; Routing authorization depends on `request_leads` alone.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws`.
Result: success, 942 jobs; `LawsIntegrationBuild.log` retains the output.

## Remaining work

The actual native request-prefix proof remains open.
Atomic stages, cleanup provenance, release history, Queue histories and timeout clauses retain their named obligations.
This landing changes no runtime behavior.
The final proof-graph projection refresh remains due after the remaining closures.
