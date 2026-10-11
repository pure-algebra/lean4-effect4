# Captured source integration

Captured finalizers now retain the actual acquisition or on-exit source constructor.
The complete native source, reply and heap chain still checks without planned dependencies.

Base: `10cc468b`.
Integrated seats: `0b96a501` and `a3f2f02b`.
`Cleanup.requestPath` remains an alias of the unchanged addresses in `Atomic.SourcePaths`.
The original Atomic and Workers statements remain unchanged.

Concept: scope-lifetime-finalization R11 and store-typing R4.
Consumers: source opportunity accounting and existing native heap history.
This refinement identifies actual source producers; it does not establish execution uniqueness.

Command: `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.CommandDebit Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Workers Effect4.Laws.Program.NativeReplies`.
Result: success, 1132 jobs; `CapturedSourceIntegrationBuild.log` retains the output.
The command debit work is checked separately before its landing.

Command: `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/RegistrationSourceAudit.lean`.
Result: 3025 declarations within `[propext, Quot.sound]`, no planned dependencies; `CapturedSourceIntegrationAudit.out` retains the output.

No runtime definition changes.
Original whole-history obligations and the final proof-graph refresh remain open.
