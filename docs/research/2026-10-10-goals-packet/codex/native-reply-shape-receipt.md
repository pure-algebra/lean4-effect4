# Native resume producer forms

The existing source-history invariant now carries the exact native resume payload forms.

Concept: scope-lifetime-finalization.
Requirement: R11.
Role: preservation.
Consumers: original Workers registration and release bounds, and Atomic source-use bounds.

`TerminalReply` is a predicate on existing primitive code, not a program representation.
Its cases are success, failure, represented reference read and the exact race-cleanup program.
`TaskAt` and `CommandAt` retain this predicate beside their existing source ownership.
`ResumeAt` permits void and exit-value countdown answers.
Native producers never construct the generic stored continuation countdown answer.

The checked producer census covers scheduler yields, completions, observers, countdowns, races, due drains, clock answers and host replies.
The original admitted-history source proof retains these restrictions through every actual decision.
The executable definitions and original scenario statements remain unchanged.
Race cleanup remains admitted; this slice imposes no race-free source restriction.

Commands:

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.NativeReplies`: passed, 509 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity`: passed, 1080 jobs.
- `LEAN_NUM_THREADS=3 lake env lean /private/tmp/SymbolicTerminalAudit.lean`: passed.
- Audit: 638 declarations within permitted axioms; zero planned goals and zero declarations modulo goals.

The helper results for owed completions, clocks and reply preparation now retain both source ownership and payload form.
Whole-history source-use uniqueness remains the next obligation.
Race-cleanup token correlation with saved yield frames remains separate release-custody work.
