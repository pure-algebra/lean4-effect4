# D1 row 153: bounded review of the merged repair

Reviewed integration pin `4bb22835` on `refactor/phase1-phase3`; merge `a3db653c489276e6941bad2acc43398b1a1ea000`, first parent `93360b3a74506e955f27e297e8b9cba5b3c66d75`, D1 parent `58e83c50efed310784a1f8f4e6cceeb28d9f698d`. Read the row-153 diff, its tests and receipt, plus only direct reference/typing/denotation definitions. No compiler, runtime, repository changes, or other agents.

**One concrete missing-premise candidate:** the newly expanded `PointTyped` can admit reference chains which runtime deliberately refuses, because it does not require the source's references to be well formed. The new redirect theorem requires that condition, but the still-open universal denotation obligation does not. This is separate from the receipt's acknowledged expansion fixed-point proof debt.

## Source evidence

- `Typed/Admission.lean:105–111`: `ProgramSource` carries a lawful signature, not `program.layerRefsWF`.
- `Typed/Admission.lean:129–133`: `PointTyped` checks `Eff.expandIn src.program e`; neither it nor its node/environment clauses demand well-formed references.
- `ReferenceTyping.lean:122–130`: expansion performs the root's fixed number of rounds unconditionally. `Program/Refs.lean:131–148,182–184` replaces a reference by its target, including another reference, and later rounds can resolve that chain.
- `Program/Refs.lean:154–160`: the actual formation rule explicitly refuses a target that is itself a reference.
- `DenoteR.lean:733–737,1181–1187`: runtime reference resolution also explicitly returns `badShapeExit` if the target is a reference; it does not follow the chain to the ultimate layer.
- `DenoteR.lean:1199ff`: the new redirect theorem takes `root.layerRefsWF = true`, which rules out that branch.
- `Typed/Assembly.lean:893–896,1452–1453`: `DenotesTyped root`, and its ledger obligation at arbitrary `root`, still quantify over every `PointTyped` point with no formation condition.

## Smallest concrete probe candidate

Use the existing test's service key and three layer occurrences, all with unit bodies:

```lean
-- U = .succeed (.lit .unit)
-- K = Test.Program.TypedSplit.key
root := .bind
  (.provideLayer (.succeed K (.nat 7)) false U)
  (.bind
    (.provideLayer (.ref [0, 0]) false U)
    (.provideLayer (.ref [1, 0, 0]) false U))
```

The targets are L0 at `[0,0]`, L1 at `[1,0,0]`, and the last occurrence L2 at `[1,1,0]`. Take the effect node at `[1,1]`, an empty point environment, and sufficient positive fuel. Its expanded layer becomes `.succeed K (.nat 7)`, so its expanded node can be checked at `pure unit`. The raw node still builds `.ref [1,0,0]`; lookup yields the reference L1, and the quoted runtime equation returns `badShapeExit`.

Proposed narrow controls: root `layerRefsWF = false`; `PointTyped` at `[1,1]` with unit result; the direct `denoteLayer` result is `pure badShapeExit`; then attempt `¬ DenotesTyped (root : ProgramSource)` by exposing that branch. **Not executed here:** these are a source-derived finite candidate and a proposed full denial, not a kernel-checked counterexample. In particular I have not completed the nested `TypedProg` inversion proof.

## What remains valid, and the smallest direction

The loaded-root reduction itself has not silently dropped the source checker: `loadsTyped_of_denotesTyped` (`Assembly.lean:1004ff`) still consumes `typeOfProgram` through `LoadsTyped`; that checker rejects this malformed root. The candidate therefore concerns the overbroad unconditional intermediate obligation, not acceptance of this program by the public loader. Carry the required formation condition either in the point/source admission contract or in the denotation statement and its consumers; derive it from the existing checked-program premise for the load. Measure that choice before changing shared predicates.

The current tests are honest about their narrower proof: `LayerRefs.loadsTyped:116` assumes `DenotesTyped`; `root_typed:96` only proves the expansion-based point certificate. The receipt explicitly retains the full denotation lemma and general expansion/target correspondence as open (`receipt-D1.md:339–344,424–427`). The memo-key inequality also correctly rules out equality with a same-site fully expanded run. No new issue was found in those qualifications, and no row-117/151 hold is re-reported here.

Receipt classification: this missing formation premise is **not named in the reviewed row-153 receipt section** (290–351) or its explicit M5 boundary (424–427). That text names the separate fixed-point/site-target lemma and the open `DenotesTyped` proof. The new redirect theorem itself correctly has the formation premise; the suspected loss is between that theorem and `PointTyped`/the unconditional `DenotesTyped` obligation. Retain as an uncompiled candidate for the next bounded Lean review.
