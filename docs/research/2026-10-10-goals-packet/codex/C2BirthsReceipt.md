# Coherent fiber births and the native mask instance

The native mask proofs now read the shared evaluator and command classification.
The classification retains one initialization per allocated id, with both allocation bounds.
Source-point ownership and the complete run stack relation remain open.

## Placement and base

Base: `19a484c02` on `codex/last-planned-goals`.
The enclosing commit is this landing's head.
Concept: reactive-scheduling, serving R11.
Question: `saved-mask-chain-runs`, role preservation, at `Effect4.Program.compiled_mask_chain_runs`.
The command reader also serves `saved-mask-region-bracket` at `Effect4.Program.compiled_region_bracket`.

Reach: native evaluation, iteration and every native command at arbitrary input machines.
The guarded command requires an exited target for `exitDone`; the existing command queue supplies this fact.
The unchanged raw command theorem remains a projection.

## Construction and consumers

`Birth` records existing machine code, the start flag, budget and context as proof data.
The spawn clause supplies the actual program, start flag, budget and parent's context.
It adds no stored program representation.

`Interferes` and `Transports` retain one table across each allocation interval.
Composition selects the original table below the intermediate allocator and the later table above it.
The legacy per-fiber interfaces project the stronger witness.
No choice principle constructs the shared table.

`Transports.maskAged` derives the existing whole-machine mask relation.
`Interferes.maskAged` specializes the evaluator classification through that reader.
`evaluateNative_keepsMask` uses this reader for its machine part.
`guarded_driveStep_maskRuns` becomes one application of the shared command classification.
Their names and statements remain unchanged.

The finite reader applies the mask instance to an actual spawn with inherited interruptibility.
The earlier raw-clear refusal remains checked.
The custody history's existing initialization consumer still compiles through its unchanged per-fiber interface.

## Verification

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.MaskRuns Test.Program.CommandFrames Test.Machine.MaskBracket Effect4.Laws.Program.ReleaseCustody.NativeMachineShape`

This build passes with 893 jobs; see `C2BirthsConsumers.log`.

`LEAN_NUM_THREADS=3 lake build Test.Program.CommandFrames Test.Dogfood.Scenario.Workers`

The integrated build passes with 1177 jobs; see `C2BirthsBuild.log`.

`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/C2BirthsAudit.lean`

The audit checks 470 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations modulo goals; see `C2BirthsAudit.out`.
`git diff --check` passes.

Measured line counts, before and after:

| Module | Before | After |
| --- | --- | --- |
| `Interference.lean` | 465 | 504 |
| `CommandFrames.lean` | 704 | 748 |
| `MaskRuns.lean` under `Laws/Program` | 292 | 291 |
| `MaskBracket.lean` under `Laws/Program` | 328 | 319 |

## Limits

The witness gives each new fiber's initialized frame, then its listed edits.
It does not yet connect that initial code to a source point or retain a parent-history derivation.
The polymorphic machine mask proof remains independent; C1's remaining generic cleanup is open.
The native nested-command condition still reads the existing primitive theorem.
B3 still must discharge the later stack's `inside` premise from an actual run.
No progress, cleanup count or host agreement follows from this classification alone.

Only proofs and readers change.
The last affected external comparison is retained in `history-behavior-sweep-receipt.md` beside this receipt.
No whole-tree battery or policy check runs.
