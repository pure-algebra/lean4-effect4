# PartitionedSemaphore scalar authoring probe receipt

The derived scalar record removes handwritten schema order and record carrier encoding from this probe.
It does not derive an identity-bearing cell.

## Change and boundary

Base: `8785c6f989f7b25df220649a238e93eda03921cb`.
Branch: `codex/partitioned-authoring-probe`.
Read the committed head with `git rev-parse codex/partitioned-authoring-probe`.
The preserved branch `codex/ref-model` remains at `c88c3e8d04b7b8b6217b7fb39ef5123b4e40cdc7`.

The edit fence contains this receipt and `docs/research/2026-10-08-partitioned-authoring-probe/`.
No production source changes.
No merge or push runs.

The independent model lives in the probe's `Model.lean` and imports `Effect4.Author`.
The stored steps and their laws live in `Probe.lean` and import `Effect4.Laws.Author`.
The scoped declaration audit lives in `Trust.lean`.
`check.sh` runs the narrow checks.
The logs retain their output.
The compiled `.olean` files remain uncommitted.

Latest (Effect 4.0.1) supplies the source in `vendor/effect-4.0.1/src/PartitionedSemaphore.ts`.
The profile restricts capacities, requests, and counters to natural numbers.
It excludes negative, fractional, and non-finite numbers.
`tryTake_eval` retains the capacity check even for malformed scalar states.
Reservation correspondence requires insufficient availability and a request within capacity.
No registration, allocation, deferred identity, wrapper execution, scheduling, fairness, progress, or host agreement follows.

## Placement

The obligations precede proof in the probe's `README.md`.
The proposed claim is `partitioned-semaphore-bookkeeping`, concept translation simulation, role simulation, requirement R10.
The probe adds no semantics registry entry or production contract.

| Probe declarations | Role | Evidence status | Scope and consumer |
| --- | --- | --- | --- |
| `initial_eval`, `available_eval`, `tryTake_eval` | helpers of the proposed R10 claim | proved | natural scalar states; corresponding source reading laws consume them |
| `reserve_eval` | helper of the proposed R10 claim | proved with explicit premises | insufficient availability and request within capacity; `reserve_reads` consumes it |
| `initial_reads`, `available_reads`, `tryTake_reads` | source reading connectors | proved | caller sources read their input encodings; concrete generated-source reader consumes construction and take |
| `reserve_reads` | source reading connector | proved with explicit premises | input readings and reservation branch premises |
| `initial_types`, `available_types`, `tryTake_types`, `reserve_types` | consumers of `step-language-typed`, R4 | proved | native atom typing and caller sources at their declared types |
| `Counts.modeledTy`, `modeledToC`, `modeledOfC`, `modeled_to_of`, `modeled_of_to` | deriving-generated schema and connector | checked | the actual scalar structure; construction, evaluation, reading, and controls consume them |

The source reading laws use `Step.sound` in `src/Effect4/Laws/Step.lean`.
The typing laws use `Step.typed_of_normal` in the same file.
The module value equations compare the saved step's evaluation with the separate model.
They establish no whole-run relation.
Their purpose serves the catalogue's next R10 slice.

## Commands and results

Run the saved command from the worktree root:

```bash
bash docs/research/2026-10-08-partitioned-authoring-probe/check.sh
```

The command exports `LEAN_NUM_THREADS=3`.
Its exact Lean commands are:

```bash
lake build Effect4.Author Effect4.Laws.Author ProofGraph.Audit ProofGraph.Axioms
lake env lean -DwarningAsError=true -o docs/research/2026-10-08-partitioned-authoring-probe/Model.olean docs/research/2026-10-08-partitioned-authoring-probe/Model.lean
LEAN_PATH=. lake env lean -DwarningAsError=true -o docs/research/2026-10-08-partitioned-authoring-probe/Probe.olean docs/research/2026-10-08-partitioned-authoring-probe/Probe.lean
LEAN_PATH=. lake env lean -DwarningAsError=true docs/research/2026-10-08-partitioned-authoring-probe/Trust.lean
```

`build.log` records the narrow prerequisite build.
`model.log` and `check.log` record the saved source checks.
`trust.log` records each named theorem's transitive axioms and the scoped declaration audit.
All commands exit zero in the retained run.
The audit uses the existing `ProofGraph.Audit.auditedFacts` and `ProofGraph.reachedAxiomsMany` helpers.
It rejects unsafe, partial, axiomatic, foreign, replaced, or bodyless declarations under the existing safe-recursor rule.
It checks the compiled model and probe modules, including deriving-generated declarations.
Its reached axioms stay within `[propext, Quot.sound]`.
The audit does not run the whole-library closure gate.

The wrong-type control requires the field setter to reject a Boolean at the natural availability field.
Finite controls check initial construction, a successful take, capacity refusal, and partial reservation.
A red state control distinguishes unmet permits from the whole requested amount.
Another red state control demonstrates why reservation belongs only inside its waiting branch.
The generated-source reader composes construction and taking through the shared source laws.

Check the two Markdown files with:

```bash
python3 scripts/check-language.py --strict docs/research/2026-10-08-partitioned-authoring-probe/README.md docs/research/2026-10-08-partitioned-authoring-probe-receipt.md
```

## Authoring findings

`deriving Modeled` supplies the schema, carrier maps, and inverse equations from one scalar structure.
`field_ref%` reads that generated field signature.
`record_step%` accepts construction fields by name in any supplied order.
Named contexts order both stored inputs and source applications.
The author writes no record carrier tuple or duplicated record field list.

The author still names each field reference, input context, source application, and module value equation.
The author still supplies source reading and typing premises.
Source reading calls still construct positional input carrier tuples.
Direct evaluation and reading calls need explicit contexts when Lean cannot infer these tuples.
The proof file exposes carrier folds with the existing transparency option.
Finite controls decode carrier results before comparing ordinary records and replies.
This avoids hidden carrier types blocking equality instance inference.
The author still provides the known record result type for construction.

## Open work

Identity-bearing whole-cell derivation remains outside the current `Modeled` domain.
The scalar record cannot replace waiter handles with natural request fields.
Partition insertion order, persistent iterator position, one-permit selection, cleanup, and refund require the next independent model.
The wrappers and their observations remain open.
The production plan must retain those boundaries before consuming this probe.
