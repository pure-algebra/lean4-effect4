# R2 cause and message foundation

The producer and settlement repair remains open.
This checkpoint preserves the existing interruption operation and adds its first-order message interpretation.
No producer emits these messages yet.

Base: `0f2d34595a690c42581289f5d8d3f35f1d5ff7d3`.
Head: the commit containing this receipt.
Evidence status: checked definitions, existing proof consumers, and admitted-program readers.
Scope: generic `FiberCore`; native guard, state, and stack-ledger consumers.

## Changes

`src/Effect4/Machine/Fibers.lean` adds `FiberEdit`, `interruptCause`, `interruptWithCause`, `applyFiberEdit`, and `applyFiberEdits`.
The message stores a target, observer, cancellation token, or fresh cause delta.
It stores no interpreter, function, predicate, or old target record.
`interruptRecord` delegates to the factored cause application.
The cause application combines the delta with the current target's cause.
Message application emits no trace.
An idle applied interruption returns an evaluation command.
The ordered fold retains command order.

Existing proofs unfold the factored application explicitly.
Their names and statements remain unchanged.
The proof repairs touch `Clauses`, `Handles`, `MaskRuns`, `Interference`, `Guard.Core`, and `Ledger`.
The new admitted-program readers apply the existing guard and finalizer-ledger laws to `interruptWithCause`.

## Placement

Concept: reactive-scheduling and scope-lifetime-finalization; R4 and R11.
Question: the approved R2 repair retains addressed edits across local write-back.
Role: runtime structure and proof-preserving factorization.
Consumer: producer migration, shared ledger settlement, and the coordinator's labelled moves.
Reach: generic interruption and message interpretation, with native proof consumers rebuilt.
Limit: no new admitted-history theorem, progress theorem, or outside-runtime correspondence.
Unlock: the shared frame ledger and the CE046 repair.
The complete placement and migration contract remains in `2026-10-11-codex-r2-message-plan.md`.

## Verification

Commands use `LEAN_NUM_THREADS=3`.

```text
lake build Effect4.Machine.Fibers Effect4.Laws.Machine.Clauses Effect4.Laws.Program.Interference Effect4.Laws.Program.Guard.NativeAssembly Effect4.Laws.Machine.StatePreservation Effect4.Laws.Program.LedgerRun
lake build Effect4.Laws.Program.LedgerFinalizer
lake build Effect4.Laws.Program.Guard.NativeAssembly Effect4.Laws.Machine.StatePreservation Effect4.Laws.Program.LedgerFinalizer
lake build Effect4.Api.Built
lake env lean -R docs/research/2026-10-10-goals-packet/codex -o .lake/build/lib/lean/MachineR2FoundationReader.olean docs/research/2026-10-10-goals-packet/codex/MachineR2FoundationReader.lean
lake env lean docs/research/2026-10-10-goals-packet/codex/MachineR2FoundationAudit.lean
```

The builds pass with 402, 371, 406, and 152 jobs respectively.
The reader compilation passes without diagnostics.
`MachineR2FoundationAudit.out` retains the exact audit result.
No proof goal or axiom enters the source.
`git diff --check` passes.

The seven source files add 90 lines and remove 39 lines.
This is an executable representation foundation, not a proof-consolidation deletion claim.

## Remaining work

Extend `Iter` with the ordered messages.
Migrate join, countdown, scope link, interruption, and token removal.
Apply messages after local write-back and before disposition.
Handle a missing owner explicitly.
Retain an owner-found connector.
Repair the countdown observer's stale waiter update.
Rebuild the shared guard, state, ledger, and labelled-move consumers.
Check CE046 against the retained pin observation.
The coordinator runs the reached behaviour gates at the executable repair sweep.
