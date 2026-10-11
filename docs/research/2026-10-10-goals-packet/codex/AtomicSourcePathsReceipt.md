# Atomic source paths

The unchanged Atomic requestPath definition now lives in a neutral source module.
Cleanup can retain its existing name through an alias.

Concept: scope-lifetime-finalization, R11.
Role: preservation.
Consumer: the six-request source opportunity census for the original Atomic cleanup goals.

Base: 0b96a501.
Module: Test.Dogfood.Scenario.Atomic.SourcePaths.
Command: LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.SourceOpportunity.
Result: 1071 jobs succeed; SourcePaths builds in 233ms.
Command: LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceOpportunityAudit.lean.
Result: 361 declarations remain within propext and Quot.sound; no modulo declarations or planned goals.
The audit includes the source module and its working opportunity consumers.

No program behavior or original scenario statement changes.
The complete execution uniqueness endpoint remains open.
