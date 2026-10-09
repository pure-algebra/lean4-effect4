# 2026-10-08 core receipt: PartitionedSemaphore bookkeeping

**The one thing to know before merging:** The aggregate proves four scalar source readings.
Reservation requires insufficient availability and a request within capacity.

## Base and head

Branch: `codex/partitioned-core`.
Base: `979be0ad8b86f356dc83aa7f6bdab46228684a32`.
Production head: `93f3fd435aa9fcaf0c9698855aae75fb42f6a949`.
This receipt follows the production commit.
The preserved branch is `codex/s1-sketch-review`, at `9460913f`.
The worktree is `/Users/pooks/.codex/worktrees/module-folds/lean4-effect4`.
No operation edits or builds the primary checkout.

## Changed files

| File | Content |
| --- | --- |
| `src/Effect4/Library/PartitionedSemaphore/Model.lean` | Import-free independent arithmetic and scalar `Model.Counts` |
| `src/Effect4/Library/PartitionedSemaphore/Cell.lean` | Derived type, derived image connector, and named field references |
| `src/Effect4/Library/PartitionedSemaphore/Data.lean` | Named input contexts and four stored steps |
| `src/Effect4/Library/PartitionedSemaphore/Steps.lean` | Four public source builders |
| `src/Effect4/Laws/Library/PartitionedSemaphore/Data.lean` | Four value equations |
| `src/Effect4/Laws/Library/PartitionedSemaphore/Steps.lean` | Four reading laws, four typing laws, and the aggregate |
| `docs/research/2026-10-08-partitioned-core-plan.md` | Frozen plan copy and placement before proof work |
| `docs/research/2026-10-08-partitioned-core-audit.lean` | Compiled declaration audit and finite controls |
| `docs/research/2026-10-08-partitioned-core-derive-control.lean` | Exact module-mode deriving refusal control |
| `docs/research/2026-10-08-partitioned-core-receipt.md` | This receipt |

## Commands and results

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Library.PartitionedSemaphore.Steps`
passes after the local string import repair.
The result is `Build completed successfully (501 jobs).`
Lake builds each owned module through this narrow target.

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-partitioned-core-audit.lean`
passes.
The finite controls cover zero construction, zero acquisition, accepted acquisition, capacity refusal, availability refusal, and reservation arithmetic.

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-partitioned-core-derive-control.lean`
passes.
Its `#guard_msgs` retains the exact reduction refusal without the string import.

`git diff --check` and `git diff --cached --check` pass.
A Python comparison reads the prototype with `git show` and compares each independent definition body.
Its result is `Independent model comparison: all four definition bodies match the checked prototype.`

The first build refuses the generated field-order proof in `Cell.lean`.
Adding `import all Init.Data.String.Defs` supplies the required reduction body.
The final build and retained refusal control verify this local repair.
The initial finite controls cannot infer carrier equality instances directly.
The final controls use the prototype's concrete decoding helpers and pass.

## Axiom output

```text
Partitioned core audit: 74 compiled declarations; allowed axioms [propext,
 Quot.sound]; core never reaches Laws; model never reaches Step or Laws
'Effect4.PartitionedSemaphore.Model.bookkeeping_agrees' depends on axioms: [propext, Quot.sound]
```

The scoped audit includes generated record, equality, and representation declarations.
It rejects forbidden compiled bodies and unexpected axioms.
It checks the core import boundary and the independent model's import boundary.
This audit is the implementation seat's check.
It is not an independent review or the whole-library gate.

## Evidence

Evidence status: proved for the four source readings and their aggregate.
Scope: finite natural counts, including zero, with exact image readings as premises.
Reservation requires `available < request` and `request <= capacity`.
The aggregate observes the scalar reply and next scalar record.
It does not observe partition identities or request delivery.

Evidence status: proved for the typing connectors under input typing and the native atom signature.
Evidence status: checked for compiled trust and import boundaries.
Evidence status: finite evaluation for the retained concrete controls.
No host execution result is claimed.

The source pin is `vendor/effect-4.0.1/src/PartitionedSemaphore.ts`.
The independent definitions retain their source locators in their docstrings.
The prototype is `git:8bb77baa:docs/research/2026-10-08-partitioned-authoring-probe/Model.lean`.
All four independent definition bodies remain identical.
`Counts` carries capacity, availability, and unmet need only.
The derivation occurs in `Cell.lean`, outside the independent model.

## Public interface

The core source module is `Effect4.Library.PartitionedSemaphore.Steps`.
The law source module is `Effect4.Laws.Library.PartitionedSemaphore.Steps`.
The namespace is `Effect4.PartitionedSemaphore`.

| Interface | Names |
| --- | --- |
| Independent state | `Model.Counts` |
| Independent operations | `Model.initial`, `Model.available`, `Model.tryTake`, `Model.reserve` |
| Derived schema | `countsTy`, `countsFields` |
| Named fields | `capacityF`, `availableF`, `waitingF` |
| Named inputs | `Data.InitialInputs`, `Data.CellInputs`, `Data.RequestInputs` |
| Stored data | `Data.initial`, `Data.available`, `Data.tryTake`, `Data.reserve` |
| Public builders | `initialStep`, `availableStep`, `tryTakeStep`, `reserveStep` |
| Value equations | `Model.initial_eval`, `Model.available_eval`, `Model.tryTake_eval`, `Model.reserve_eval` |
| Source readings | `Model.initial_reads`, `Model.available_reads`, `Model.tryTake_reads`, `Model.reserve_reads` |
| Typing connectors | `initial_types`, `available_types`, `tryTake_types`, `reserve_types` |
| Registry pointer | `Model.bookkeeping_agrees` |

## Landed theorems and their placement

The following groups retain the five fields from the pre-work plan.
Every name below uses the namespace `Effect4.PartitionedSemaphore`.

### Value equations

- Concept: `translation-simulation`; property: scalar source readings agree with the independent model.
- Question: `partitioned-semaphore-bookkeeping`, role simulation; consumers: the corresponding `Model.*_reads` laws.
- Reach: `Model.initial_eval`, `Model.available_eval`, `Model.tryTake_eval`, and `Model.reserve_eval` evaluate stored steps at natural scalar inputs.
- Does not establish: input readings, allocation, identity, waiting, schedules, progress, or host execution.
- Unlocks: R10 through the corresponding source reading law.

The reservation equation retains the same branch premises as its source consumer.

### Source readings and aggregate

- Concept: `translation-simulation`; property: source observations agree with independent scalar bookkeeping.
- Question: `partitioned-semaphore-bookkeeping`, role simulation; pointer: `Model.bookkeeping_agrees`.
- Reach: `Model.initial_reads`, `Model.available_reads`, `Model.tryTake_reads`, and `Model.reserve_reads` assume input readings of exact images.
- Does not establish: full module behavior, allocation, cancellation, delivery, scheduling, progress, codec admission, or host execution.
- Unlocks: R10 and later waiting composition.

The aggregate consumes all four source reading laws.
It universally quantifies their inputs, environments, paths, and values.
Its reservation component retains both branch premises.
Decisions rows 330, 331, 333, and 335 bound these statements.
The coordinator places the concrete pointer in the integration semantics registry before this proof work.

### Typing connectors

- Concept: `store-typing`; property: stored steps produce their declared source types.
- Question: `step-language-typed`, role compatibility; consumers: checked Ref callback callers in the later composition slice.
- Reach: `initial_types`, `available_types`, `tryTake_types`, and `reserve_types` assume declared input types and the native atom signature.
- Does not establish: membership, codec admission, handle validity, observation agreement, or host behavior.
- Unlocks: R4 through concrete readers of `Step.typed_of_normal`.

## Shared authoring findings

The stored data uses named fields and named inputs.
The source builders reuse `Step.term`.
The reading and typing proofs reuse `Step.sound` and `Step.typed_of_normal`.
No shared semantics are duplicated.

A module-mode deriving client needs the local string definition import for the generated field-order proof.
Existing deriving clients `Test.Schema.Modeled` and `Effect4.Laws.Author.Explain` are non-module clients.
Neither client needs that local import.
The retained refusal control names the exact gap.
A later shared derivation repair could remove this author burden without changing the arithmetic.

The source connectors repeat image input packaging and the stored step's reading check.
A future shared authoring helper could package those inputs and expose the check once.
A future concrete comparison helper could hide carrier equality inference for finite controls.
These are proposals for the shared organization seat, not changes in this slice.

## Open obligations

The coordinator owns root reachability, the semantics registry join, public machine controls, emission controls, and independent review.
This branch supplies no root import edit.
Waiting, release, partition queues, registration, cancellation, delivery, and wrapper composition remain outside this slice.
Membership, codec admission, and identity validity remain separate claims.
No full sweep runs and no branch is pushed.

## Proposed decisions rows

None.
