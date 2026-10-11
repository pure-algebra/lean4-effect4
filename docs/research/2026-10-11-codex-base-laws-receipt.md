# Machine base laws: native field sweep

The initial sweep keeps 61 theorem statements and removes 278 source lines overall.
The original scenario goals remain open where their history or source-use obligations remain planned.

Base: `5df94b30`. Head: the commit containing this receipt.
The shared base integration is `7c69f880`; initialization retention is `5df94b30`.
Their receipts are in the goals packet's `codex/` folder.

## Placement and changed modules

Concept: reactive-scheduling, with the existing guard preservation consumers.
The registry claim `stepped-fiber-live` consumes the guard state and queue laws.
The frame instances also serve scope-lifetime-finalization through `saved-mask-chain-runs`.
Reach: the same native evaluator, iteration, interpreters, fibers, row tables and hypotheses as before.
Limits: the sweep proves no new progress, host observation, source uniqueness, or whole-history obligation.

The rewritten chains cover interrupted cause, deferred cause, identity, exit, running, pending shape, ready outcome, fresh park, and fresh fiber counter.
`DeferredCause` imports the original interruption facts instead of repeating five proofs.
`FrameMoves` owns the move relation and its induction.
`Footprint` owns the evaluator's frame and stable-field classification.
`Moves` keeps the existing projection interfaces, without repeating that classification.
`Parking` classifies unchanged waiting fields or a newly installed pending entry, token and outcome.
`ReturnFields` derives its three waiting judgments from that classification.
`NativeStateMotion` derives counter growth from `Interferes`.

The table includes added modules, so the net reduction includes their cost.

| Module | Before | After | Removed |
| --- | ---: | ---: | ---: |
| `src/Effect4/Laws/Program/Guard/Interruption.lean` | 415 | 309 | 106 |
| `src/Effect4/Laws/Program/Guard/DeferredCause.lean` | 224 | 154 | 70 |
| `src/Effect4/Laws/Program/Guard/ReturnFields.lean` | 450 | 311 | 139 |
| `src/Effect4/Laws/Program/Guard/NativeStateMotion.lean` | 108 | 76 | 32 |
| `src/Effect4/Laws/Program/Moves.lean` | 300 | 75 | 225 |
| `src/Effect4/Laws/Program/MovesConnect.lean` | 151 | 119 | 32 |
| `src/Effect4/Laws/Program/Footprint.lean` | 264 | 264 | 0 |
| `src/Effect4/Laws/Program/FrameMoves.lean` | 0 | 113 | -113 |
| `src/Effect4/Laws/Program/Parking.lean` | 0 | 213 | -213 |

## Verification

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Routing Test.Dogfood.Proofs.HostTimeoutSettle`: passed, 1429 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/C1Audit.lean`: passed.
- The audit reports 530 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
- The statement comparison against `5df94b30` reports 61 unchanged signatures.
- `git diff --check`: passed.

`C1Build.log`, `C1Audit.out`, `C1Statements.tsv`, and `C1LineCounts.tsv` retain the measurements in the goals packet's `codex/` folder.
An earlier build named `Test.Dogfood.HostTimeoutSettle`, which does not exist.
The corrected command above completed successfully.

## Open obligations and deferred gates

This is the native field portion of C1, including the park-outcome portion needed from C2.
The coupled source, queue, store and command chains remain with their current owners.
`MaskRuns` remains polymorphic and includes other fibers, nested commands and finished outcomes.
The native frame projection alone cannot replace its full theorem statements.
Its consolidation needs the generic outcome and live-command classification.
The classification must still exclude stack clearing for live fibers and retain complete spawn provenance.
Run stack locality, source points, and stack paths remain open.
The services chain still waits for the context ruling.

No behavior gate is run during this proof-only sweep.
The previously scheduled behavior pass remains after the major scenario proof structures.
The full battery, policy and whole-tree axiom gates are not run.
No runtime, source language or original scenario statement changes here.

## Completed-outcome extension

[C2FinishedReceipt.md](2026-10-10-goals-packet/codex/C2FinishedReceipt.md) records the next checked landing.
The shared outcome census now retains the finishing frame step.
The native mask proof consumes that witness and the existing moves.
The receipt retains its narrow build, audit, changed files and measured line counts.
Its raw-command control establishes why live-frame classification needs the existing command authority.
The original scenario and remaining base-law obligations stay open as recorded above.

## Guarded live command words

The native command census now retains clearing-free words for live fibers.
The raw frame theorem projects the same census.
See [the checked receipt](2026-10-10-goals-packet/codex/C2LiveCommandsReceipt.md).
The complete birth witness and run stack relation remain open.

## Coherent births and the native mask connection

The evaluator and command classifications now retain one initialization per allocated fiber id.
The native whole-machine mask relation follows from this witness.
The native command mask proof now reads the shared classification.
See [the checked receipt](2026-10-10-goals-packet/codex/C2BirthsReceipt.md).
Source-point birth ownership, the polymorphic cleanup and the run stack relation remain open.
