# Shared accounting integration receipt

The combined law graph builds before the outer-history consolidation starts.
The operation-counter instance reads the actual shared command proof.
It supplies no timeout progress or command-room conclusion.

## Placement

Concept: reactive-scheduling and scope-lifetime-finalization, R11.
Question: the two Timeout numeric history claims need actual operation accounting.
Consumer: the count-entry prefix reads the selected owner counter after actual commands.
Reach: one actual command, native evaluation, and distinct stored fiber identifiers.
The command proof adds at most its selected owner loop allowance.
No new command case analysis appears in the instance.
Public command room, source progress, and completed cleanup remain open.

## Sources and checks

The combined build uses source head 21f020782.
It passes 1514 jobs, including Effect4.Laws, Timeout readers, and Atomic.WriterMachine.
The callback refinement uses source head 1692a1ba67826421520c92ed3c9868120d0d4516.
Its direct consumer build passes 1156 jobs.
The production reader passes on the refined source.
Its eight-module audit passes 537 declarations within [propext, Quot.sound].
It reports zero goals and zero declarations modulo goals.
The operation ledger, command instance, and actual command reader compile against those same libraries.
Their audit passes 29 declarations at the same ceiling, with zero goals and zero declarations modulo goals.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Audit.RuntimeCoverage Test.Dogfood.Proofs.HostTimeoutLocalSteps Test.Dogfood.Proofs.HostTimeoutNumberFlow Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Proofs.HostTimeoutNumberCounted Test.Dogfood.Scenario.Atomic.WriterMachine
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.PlaceFunding.Commands Effect4.Laws.Program.LedgerFinalizer Test.Dogfood.Scenario.Atomic.WriterMachine
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/place-funding/PromotionReader.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/place-funding/PromotionAudit.lean
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-11-machine-models/codex/place-funding/CheckCounterCurrent.py
```

IntegrationEvidence.json records source heads and evidence hashes.
The retained logs record the actual commands and results.
CheckCounterCurrent.py rebuilds the counter readers against the current repository libraries.
This slice changes research evidence only.
No executable behavior changes, so no behavior gate runs.
The original open goals remain open.
