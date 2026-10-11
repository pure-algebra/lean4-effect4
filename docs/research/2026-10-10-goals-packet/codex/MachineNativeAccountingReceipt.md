# Native frame and scope-response debit

The original Workers release bound remains open. This slice closes actual frame delegation and synchronous operation accounting.

Base: ff35624f. The source module is `Effect4.Laws.Program.ReleaseCustody.NativeAccounting`.

## Placement

1. Concept: scope-lifetime-finalization. The helpers serve R11 release custody.
2. Question: `Execution.history` supplies `Workers.Assertions.releases_step`. These helpers feed its native evaluator debit.
3. Reach: every actual primitive frame step, and actual synchronous operation responses under unique scope keys, freshness and checked frame sequencing.
4. Limit: this slice proves no full evaluator, command or history closure. It changes no scenario statement or host admission rule.
5. Unlock: `IterDebit` combines these clauses with the actual selected-owner installation and settle adapter.

## Evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.NativeAccounting` passes, 443 jobs.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachineNativeAccounting.lean` passes.

The reader applies the laws at actual `Api.Built` frame evaluation and actual scope-add responses.

The axiom audit checks 105 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.

Open work: fiber actions, complete evaluator accounting, command shape closure and original history funding. No behaviour gate runs in this proof-only slice.
