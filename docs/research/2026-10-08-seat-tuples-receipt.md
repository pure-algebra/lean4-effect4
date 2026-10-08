# Generic typed tuples receipt

The coordinator adds `Test.Program.StepTuples` to the test root.
`Effect4.Laws.Modules.Step` already reaches the new tuple helper module.
This slice changes no root, registry, ruling, `Eff`, or `Term` declaration.

The base is `9fbe735f`. The checked source commit is `62437bcb` on `codex/module-tuples`.

## Change

`Step.tuple` replaces the arity-specific constructors in `src/Effect4/Modules/Step.lean`.
`StepItems` stores one typed child per declared item type.
`ItemResults` carries those children through each Step algebra.
`tupleShape` selects the existing product type for exactly two items.
Other lengths retain the existing tuple type and required-column carrier.
`tuple2` and `tuple3` remain transparent compatibility builders.
Their result types, flat term shapes, and typing facts retain the previous interfaces.

`packTuple` drops the terminal column unit only at the two-item product boundary.
The other lengths retain the required-column carrier.
The native term and value remain flat ordered item lists.
No identity, source name, runtime object, function, or expression enters stored syntax.

The shared laws extend to the item fold.
The existing public reading, typing, framing, scope, renaming, and annotation-erasure statements remain available.
`Step.frame_at` handles the generic result index before the existing record-result frame theorem applies.
It uses the generated mutual recursor.
The public `Step.frame` statement remains unchanged.

## Placement

The image and reading helpers serve `step-language-sound`, translation-simulation, R10.
The tuple arm of `Step.sound_core` consumes them.
Module agreement laws consume the public reading law.

The normalization and typing helpers serve `step-language-typed`, store-typing, R4.
The tuple arm of `Step.typed_core` consumes them.
Queue operation typing consumes the public typing law.

The scope helper serves `operation-data-scoped`, initial-algebras-folds, R4.
Module scope evidence consumes it before `Api.Author.build`.
The frame helper serves `step-frame`, translation-simulation, R10.
The existing `Step.frame` consumes it.
Renaming and annotation erasure retain their existing module and authoring consumers.

Reading requires canonical field names and the existing structural requirements.
Folds require scope alignment. Deferred comparisons require an identity capability.
Typing requires the existing normalization and formation facts, or their Boolean check.
These statements establish no checked `Modeled` tuple admission, allocation, progress, or target execution.

## Changed files

- `src/Effect4/Modules/Step.lean`
- `src/Effect4/Modules/Step/Rename.lean`
- `src/Effect4/Laws/Modules/Step.lean`
- `src/Effect4/Laws/Modules/Step/Requirements.lean`
- `src/Effect4/Laws/Modules/Step/Scope.lean`
- `src/Effect4/Laws/Modules/Step/Rename.lean`
- `src/Effect4/Laws/Modules/Step/ErasedCompiler.lean`
- `src/Effect4/Laws/Modules/Tuples.lean`
- `Test/Program/StepTuples.lean`
- `docs/research/2026-10-08-seat-tuples-plan.md`
- this receipt

## Checks

```text
LEAN_NUM_THREADS=3 lake build Effect4.Modules.Step
passed: 71 jobs

LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Tuples
passed: 479 jobs

LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Step.Requirements
passed: 480 jobs

LEAN_NUM_THREADS=3 lake build Test.Program.StepTuples Test.Program.QueueData Test.Program.QueueAgreement Test.Program.StepInputs Test.Program.StepFolds Test.Program.StepConstructors
passed: 870 jobs

LEAN_NUM_THREADS=3 lake build Test.Program.StepTuples
passed: 863 jobs, with the final expanded controls

LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-tuples-trust.lean
passed: ten selected public guarantees and tuple helpers reach only propext and Quot.sound

LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-tuples-audit.lean
passed: every declaration of all nine changed semantic and test modules
870 declarations; reached [propext, Quot.sound]

 git diff --check
passed
```

The complete audit uses `ProofGraph.Audit.auditedFacts` and `ProofGraph.reachedAxiomsMany`.
It checks unsafe, partial, axiom, external, replacement, and bodyless opaque flags under the existing safe-recursor policy.
It refuses missing declarations, exhausted traversal budgets, and any axiom beyond `propext` and `Quot.sound`.
It audits no Lean elaborator module; this slice changes none.

The tuple battery reads and types lengths zero through four.
It pins the two-item and three-item term shapes.
It refuses a mistyped item and a two-item tuple type that conflicts with native normalization.
It checks the union normalization boundary and noncanonical record reads.
It applies the shared laws to a nested fold and a renamed generic payload.
These are Lean readers and finite controls. No host run occurs.

## Remaining work

The tuple slice has no unproved local obligation.
The coordinator owns the test-root import and combined integration audit.
Old Queue Steps and Typing proof failures remain separate migration work.
The Queue seat confirms those failures predate this tuple slice.
`QueueData` and `QueueAgreement` pass unchanged here.
The checked `Modeled` domain still refuses tuple types.
The host boundary remains unchanged.

## Interim triple helper cleanup

The coordinator requests removal of unused interim triple image and reading helpers.
The Queue seat confirms neither helper has an in-flight consumer.
`Step.eval_tuple3` moves unchanged into `src/Effect4/Laws/Modules/Tuples.lean`.
The tuple battery applies it at the original flat triple carrier.
`src/Effect4/Laws/Modules/Tuple3.lean` and its shared Step import are removed.
The native `reads_tuple3` and `types_tuple3` helpers remain unchanged.

```text
LEAN_NUM_THREADS=3 lake build Test.Program.StepTuples Test.Program.QueueData Test.Program.QueueAgreement
passed: 866 jobs

LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-tuples-audit.lean
passed: 871 declarations in nine changed modules; reached [propext, Quot.sound]

LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-authoring-boundary-review.lean
passed: a descending-name record constructs, then fails canonical and normal checks
```

The last probe clarifies the author guide's boundary. Elaboration checks named field construction.
The Step checks retain canonical-name and formation conditions.
The coordinator owns the wording correction.
