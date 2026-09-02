# Effect runtime coverage

This document owns the definition, vocabulary, and reporting format of the
Effect v4 runtime coverage metric. Numbers live in generated and emitted
facts, never here. Read this before quoting, changing, or extending coverage.

## What the metric measures

Coverage is the share of pinned Effect runtime *behaviours* that have a Lean
witness. It is not an implementation checklist and not an equivalence claim.
A behaviour is a mechanism a cold reader could observe in the pinned source:
which continuation arms a frame answers, when a deferred interrupt is noticed,
which forks a parent interrupts on exit, in what order a scope closes.

Three artefacts carry it:

| Artefact | Role | Owner |
| --- | --- | --- |
| `generated/effect-runtime-census.tsv` | the denominator: one row per behaviour, anchored to the pinned bytes with a span digest | `scripts/generate-effect-runtime-census.sh` |
| `Effect4Test/Audit/RuntimeCoverage.lean` | the numerator: the frozen row list with disposition, coverage state, witnesses, receipts, and exact witness statements | authored, test-side |
| `scripts/check-effect-runtime-census.sh` | the gate: byte drift of the census and the join between census and Lean rows | CI step |

The pinned source is `effect@4.0.0-rc.112` as vendored under
`vendor/effect-4.0.0-rc.112/src/`; the generator refuses any other bytes.
The reading of that source is `docs/effect-rc112-fiber-runtime.html`.

## Vocabulary

**Row kinds** (`kind` column, fixed): `op`, `frame-arm`, `checkpoint`,
`interrupt`, `fork`, `scope`, `scheduler`, `exit`, `cause`, `entry`, `rule`.
A row id is `<kind>.<kebab-name>` and is stable for the life of the census.

**Disposition** is the `PORT-MANIFEST.md` vocabulary and answers who owns the
behaviour's carrier. `targetOnly`, `excludedInternal`, and `evidenceOnly`
rows are outside the denominator and may carry no witness. Every other
disposition counts. `owned` rows must carry at least one witness.

**Coverage state** answers what Effect4 has proved about the row today:

| State | Meaning | Rule |
| --- | --- | --- |
| `absent` | no witness | the only state allowed with an empty witness list |
| `partial` | at least one witness, but some clause of the row's summary line has no theorem | must list what is missing in the row's comment |
| `green` | every clause of the row's summary line is a named theorem over the Effect4 model, with an axiom receipt inside `propext`/`Quot.sound` | never declared to make a number move |

The green criterion is clause-by-clause against the census summary. A finite
probe, a compile, a test, or a theorem about the Lean model's own invariants
does not turn a clause green. When in doubt the state is `partial`; a metric
whose first green row is arguable is worse than one with none.

**Witness**: a Lean `theorem` (never a `def`, never a Prop-typed def) whose
exact statement is frozen in the module's `StatementSnapshot` section by
`#check (@name : proposition)` ascription, and whose kernel receipt is
`none`, `propext`, `Quot.sound`, or `propext,Quot.sound`.

## The report format

The only sanctioned way to state coverage is the line produced by

```bash
./scripts/report-effect-runtime-coverage.sh
```

which runs the Lean emit and prints, from the emitted `coverage` row:

```
Effect rc.112 runtime coverage: denominator <D>; owned-with-green <O>/<D>;
green <G>, partial <P>, absent <A>; census <total> rows, <E> excluded
partial: <ids>
```

Quote that block verbatim, with the commit it was produced at. Do not compute
a percentage by hand, do not round, and do not describe a row as covered in
prose unless it is `green` in the module. "Owned-with-green over the
denominator" is the headline pair; the other counts are context.

A handoff, plan row, or pull request that mentions coverage links the gate
run and pastes the block. It never restates numbers from memory or from an
earlier session.

## How the number moves

**Adding a witness** happens in `Effect4Test/Audit/RuntimeCoverage.lean` only:

1. add the theorem name and its receipt to the row's `witnesses`;
2. add the exact statement as a `#check (@…` ascription, transcribed from
   `#check @name`, and append the name to `snapshotWitnesses` in the same
   order;
3. change the row's coverage state only if the green criterion is met;
4. keep `expectedRowTotal` and `expectedDenominator` true;
5. run `./scripts/check-effect-runtime-census.sh`.

The module fails the build on a missing witness, a non-theorem, a statement
mismatch, an axiom drift, a duplicate id, an owned row without a witness, a
witness on an excluded row, or a snapshot that does not match the used
witness set in both directions.

**Adding or re-pinning a census row** happens in the generator only. A row is
`kind|id|file|anchor|offset-start|offset-end|expected-span-sha256|summary`,
where the anchor must occur exactly once in its file. Add the row, add the
matching Lean row with disposition `absent` and no witness, update the
per-kind counts and totals in both places, regenerate the projection with the
recorded command, and run the gate. A digest that drifts because upstream
changed is a deliberate re-pin: the whole pin moves together, never one row.

**A new theorem in `Effect4/`** intended as a witness still passes through the
normal packet discipline, and any public declaration added to
`Effect4/Concurrency/*` also moves the frozen surface census in
`Effect4Test/Concurrency/FiberAssurance.lean` and its generator counts. Plan
both edits together.

## Path to full coverage

Coverage rises by building models, not by relabelling rows. Row families at
census v1 and the model that closes each:

| Family | Rows | Model that closes them |
| --- | ---: | --- |
| `cause.*`, `exit.*`, `rule.cause-has-no-structure` | 11 | `Effect4/Semantics/Cause.lean`, `Exit.lean`: flat reasons, union combine, squash, finalizer merge |
| `scope.*`, `rule.scope-close-lifo-state-first` | 15 | `Effect4/Runtime/Scope.lean`: state machine, LIFO close, sequential and parallel close, fork linkage |
| `fork.*`, `interrupt.accumulate`, the two fork rules | 14 | `Effect4/Concurrency/Supervision.lean` and `Race.lean`: tracked versus daemon children, parent-exit interruption, scope-bound fibers, live-join resumption |
| continuation-machine `op.*`, `frame-arm.*`, `checkpoint.*`, and the stack rules | 30 | a new continuation-stack calculus: frames with three arms, `getCont` with the ensure hook, deferred-interrupt flag, handler skipping, yield versus park |
| the seven `partial` rows | 7 | finish once the models above exist; each also needs one scheduler refinement |

The three `foreignBoundary` rows (`op.WithFiber`, `op.YieldableError`,
`cause.annotations`) close with a registered boundary identity and a refusal
theorem, not a behavioural model.

Take the exact current row counts from the census, never from this table.
