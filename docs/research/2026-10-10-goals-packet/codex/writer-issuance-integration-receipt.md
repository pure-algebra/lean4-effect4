# Native writer issuance integration

Atomic's numeric log-history endpoint remains open; its native writer and settlement dependencies now share the checked scalar laws.

Base: `de348b6b1`.
Integrated checkpoint: `c55d70ba9`, landed as `a48c72c20`.
The commit containing this receipt records the integration head.

Concept: scope-lifetime-finalization, R11.
Consumers: Atomic cleanup log debits and existing source-opportunity history.

`WriterWeights` owns native issuance, settlement, mask, and fork scalar bounds.
`SourceOpportunityExecution.settle_debit` consumes the shared settlement law with its statement unchanged.
The Atomic modules consume actual sync writes, frame evaluation, finalizer dispatch, and local settlement.
`Test/All.lean` reaches those modules through `Atomic.WriterMachine`.

Command: `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic.WriterMachine Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.QueueWorkers Effect4.Laws.Program.SourceOpportunityHistory`.
Result: passed, 1205 jobs.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AtomicWriterIssuanceAudit.lean`.
Result: 127 declarations within `[propext, Quot.sound]`, no planned goals, and no declarations modulo goals.
The adjacent build log and audit output retain these results.

Full command and admitted-history composition still must replace `Atomic.Cleanup.log_debits`.
This proof-only integration changes no runtime behaviour and reaches no behaviour gate.
