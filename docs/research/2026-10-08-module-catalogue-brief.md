# Brief: author as many composed modules as the step language allows

Status: brief for Codex (history, not authority). Base: the commit of cutover slice C2 on
`refactor/phase1-phase3`, which moved the composed modules to `src/Effect4/Library/`. Owner,
2026-10-08: author as many modules as possible with the step language, to keep finding where the
interfaces and the ergonomics should settle. Be honest about the gaps.

## The one thing to know first

Each module is a probe of the interface as much as a product. Its receipt lists every place where
the author repeated work, wrote positions, or proved by cases what a shared law should give. That
list is the output the owner wants, beside the module.

## The catalogue, in order

Sizes are the line counts of latest (Effect 4.0.1), at `vendor/effect-4.0.1/src/<M>.ts`, mostly
documentation. "Today" means the step language, named inputs, the list builders and the existing
operation forms, with no new wrapper.

The order follows latest's own building blocks, upward
(`docs/research/2026-10-08-effect-building-blocks.md`): a module comes after what it is built from.

| Order | Module | Built from, in latest | Today | It tests | Blocked part, by gap |
| --- | --- | --- | --- | --- | --- |
| 1 | `Ref` (1672) | `MutableRef` | all | the smallest cell; `modify`, `getAndUpdate` as steps | none |
| 2 | `PartitionedSemaphore` (805) | a keyed map of permits | all | a keyed cell; reuse of the Semaphore's steps | none |
| 3 | `PubSub` (3459), bounded strategy first | `Deferred`, `Latch`, `MutableList`, `Scope` | the pure steps | subscribers as a list, the publish fold, three strategies as one step each | wake delivery, G1 |
| 4 | `SynchronizedRef` (1269) | `Ref`, `Semaphore` | the pure `modify` | a client's program inside the lock | G5 |
| 5 | `RcRef` (244), `RcMap` (1245) | `Deferred`, `Fiber`, `Scope` | the counting steps | a reference count as a step | finalizers, G7 |
| 6 | `FiberSet`, `FiberMap`, `FiberHandle` | `Deferred`, `Fiber` | the bookkeeping steps | fibers as entries of a cell | interruption delivery, G1 |
| 7 | `Cache` (2684) | `Deferred`, a map | the map steps | a map of deferred entries; the identity table | time to live, G6; the lookup program, G5 |
| 8 | `Pull`, then `Channel` | `Effect`; then `Queue`, `PubSub`, `Latch`, `Semaphore`, `Scope`, `Fiber` | the pull protocol | a pull transformer as a stored definition with captures (row 331) | the pullLoop wrapper, G1 |
| 9 | `SubscriptionRef` (2105) | `PubSub`, `Semaphore`, `Stream` | the steps | the first module built from two others | the composition law, G10 |
| 10 | `TxRef` (474), `TxQueue` (1880), `TxSemaphore` (1177) | `TxRef`, over `Effect.tx` | none | the attempt as one step | G4 |

Stop at a gap. Write the module's pure steps and model, and prove its value equations. Record
the blocked operations in the receipt with their gap's number.

## The gaps, honestly

| Gap | What is missing | State |
| --- | --- | --- |
| G1 | named wrapper reply records, and one law per wrapper: atomic, waitRetry, waitAnswer, scheduled | operations are assembled by hand; wrappers have scope and typing laws only |
| G2 | the module form, `module Q mirrors "Q.ts"` (row 331) | not built |
| G3 | `derive_step` with its certificate | probe DERIVE-1 only; each value equation is proved by hand |
| G4 | the transaction attempt as one machine step (row 331) | not built |
| G5 | a client's program run by a module, in the law's observation (row 333, point 2) | ruled; no wrapper |
| G6 | the scheduled wrapper and time to live | the machine has timers; no wrapper |
| G7 | finalizers of a module's scope | `scoped` and `acquireRelease` exist in `Eff`; no wrapper |
| G8 | subterm sharing in a step's term | `Term` has no local binding; Pool's lease is 167 nodes |
| G9 | identity tables with injectivity (slice L6) | carried as a premise |
| G10 | the module law: agreement across schedules (row 329) | open |

## Where a module's files go (decisions row 332)

| File | Holds | Exposure |
| --- | --- | --- |
| `src/Effect4/Library/<M>/Model.lean` | the model, transcribed from latest by line; a `module` file with no law | module library |
| `src/Effect4/Library/<M>/{Cell,Data,Steps,Ops}.lean` | the cell, the records and passes, the step terms, the operations | module library |
| `src/Effect4/Laws/Library/<M>/` | the value, reading, typing and agreement laws, and the model's own laws | proof |
| `Test/Program/<M>*.lean` | the batteries, reached from `Test/All.lean` | test |

- Import the step language from `Effect4.Step` and its parts, and the shared pieces from
  `Effect4.Library.Words`, `Effect4.Library.Waiting` and `Effect4.Library.Table`.
- Import the shared laws from `Effect4.Laws.Step` and `Effect4.Laws.Step.*`.
- Add the module's model and operations to `src/Effect4/Library.lean`, and its laws to
  `src/Effect4/Laws.lean`, at the end of each list.
- Add the module's two areas and its `("src/Effect4/Library/<M>", .library)` exposure to
  `tools/Tools/ArchitectureRoles.lean`.
- Report the landing's reuse ratio and load-bearing count with `#load_report` on the module's
  law prefix (`tools/Tools/LoadPaths.lean`).

## Rules for each module

- The model transcribes latest by line (`AGENTS.md`, row 331) and never reads the step.
- A heartbeat raise in a value proof is a finding: name the step and the carrier it unfolds.
  The fold slice added five, in the Queue's and the Pool's typing and data laws.
- One receipt per module, with the obligations placed by the five fields of `AGENTS.md`.
- Narrow builds only. No sweep, no push.
