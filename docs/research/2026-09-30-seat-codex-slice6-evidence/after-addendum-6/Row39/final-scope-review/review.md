# Slice 6 final source scope review

Compared `c42f4a46ab9b1e5ed6c852fa4acb63832edc4d0b` to `8cdc931b0192b2808c4e9c301752704eeff0c91a`. The worktree was clean at this snapshot. Research copies are excluded from all source/proof inventories. No compiler, generator, or previously completed byte validator was run.

Two comment corrections are indicated; no implementation scope or trust-construct violation was found.

## Concrete comment corrections

1. `src/Effect4/Laws/Program/Typed/Assembly.lean:338–342` still says the current capstone remains refuted by E4-PROV-CE-005, E4-PROV-CE-006 and E4-SCHED-CE-016. The live register marks those attacks REPAIRED by F/G/H1; the earlier failures are retained against historical clauses. Replace this assertion with historical-obstruction wording and retain the open initialization/transition/reachability disclaimer. No theorem or contract change is indicated.
2. `Test/Counterexamples/Machine/Semantics/M6Capstone.lean:17,46–47` calls the host-answer reachability predicate and its refutation existing/current, although the formula explicitly uses the locally retained `ReviewedRReachable`. Say reviewed former statement. The stable theorem name `current_m6_capstone_false` need not change. These comments predate this commit range but are in the touched battery.

## Ownership and completion boundaries

- Unchanged: lakefile.toml; README/AGENTS; docs/STATE, docs/core (including decisions), ARCHITECTURE, GENERATED, DESIGN-BASIS/ISSUES/MAP, RUNTIME-COVERAGE; Test/contracts; tools/Tools/ArchitectureRoles. The coordinator prose edits remain proposals only.
- Changed special anchors: src/Effect4.lean and src/Effect4/Laws.lean lose the retired imports; Test/All loses retired batteries and adds G LayerValue beside M6Capstone and H2PartOne immediately after TypedControl; Test/Audit/AxiomGate removes exactly the five retired public names and one private renderer exception. No exception is added or widened.
- Counterexample registers are authorized bookkeeping: G/H1/H2 repair/evidence rows and the 21 row-39 archive moves. No decisions-register edit occurs.
- G: checker/judgment leaves and their matching proofs change; the receipt limits corpus evidence to 408 finite verdicts and the earlier g141 refusal. No extra completion claim was found.
- H1: only proof-side state/queue conditions and adapters change. StepPreserves retains the explicit running dispatch premise. The two lift adapters require all command facts; H1-RCODE-SITES and the 18 command facts remain open.
- H2: ExitOk excludes badName/notImplemented at typed exit positions and buffered race failures. Base Membership is untouched. Missing-service exclusion remains part two. The receipt accurately records nine existing source-body repairs and 43 changed test bodies; it does not claim run-wide defect avoidance or M5/M6 proof completion.
- Row 39: four ordered source commits after H2. Receipt calls them source checkpoints, with the producer chain and final comparisons pending. No premature regenerated-integration claim occurs. Row 8 duplicate-key semantics and addresses remain outside this deletion/relocation series.

## Exact static checks

- `git diff --check c42f4a46 8cdc931b -- . ":(exclude)docs/research/**"`: exit 0. The unfiltered command reports whitespace in retained research patch/log artifacts (including required patch-context spaces); these historical copies are outside this source check.
- Read-only commit/path inventory: 7 commits, listed below; full structured result in checks.json.
- Added/replaced active text from 24 surviving changed src files: 626 nonblank active lines. Nested comments and strings masked; no new sorry, partial, unsafe, native_decide, axiom, extern, implemented_by, simp_all, try or first-fallback construct found. This is lexical checking, not a substitute for the retained axiom gate.
- Protected-path diff is empty. Runtime Machine source and the base Membership module do not change in this range.

## Actual paths by slice

### 57c93ba4 — Require layer values to fit their service carriers

11 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M Test/All.lean
A Test/Counterexamples/Machine/Semantics/LayerValue.lean
M Test/Counterexamples/REGISTER.md
M Test/Program/AuthorContract.lean
M Test/Program/ProvisionContract.lean
M generated/corpus-index.tsv
M src/Effect4/Laws/Program/Typing/CheckInversion.lean
M src/Effect4/Laws/Program/Typing/CheckSound.lean
M src/Effect4/Laws/Program/Typing/HasTy.lean
M src/Effect4/Program/Checker.lean
M src/Effect4/Program/Provision.lean
```

### d554cd71 — Type queued completions and respect halted dispatch boundaries

7 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M Test/Counterexamples/Machine/Semantics/M6Capstone.lean
M Test/Counterexamples/Machine/Semantics/ValueMembership.lean
M Test/Counterexamples/REGISTER.md
M src/Effect4/Laws/Program/Guard/Core.lean
M src/Effect4/Laws/Program/Guard/RegistrationQueue.lean
M src/Effect4/Laws/Program/Typed/Assembly.lean
A src/Effect4/Laws/Program/Typed/Scheduler.lean
```

### abc7b124 — Exclude shape defects at shared typed exit boundaries

16 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M Test/All.lean
M Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean
M Test/Counterexamples/Machine/Semantics/M6Capstone.lean
M Test/Counterexamples/Machine/Semantics/TrivialPosts.lean
M Test/Counterexamples/Machine/Semantics/ValueMembership.lean
M Test/Counterexamples/REGISTER.md
A Test/Program/H2PartOne.lean
M Test/Program/LoadedAdmission.lean
M Test/Program/TypedControl.lean
M Test/Program/TypedResidual.lean
M Test/Program/TypedStack.lean
M src/Effect4/Laws/Program/Typed/Admission.lean
M src/Effect4/Laws/Program/Typed/Assembly.lean
M src/Effect4/Laws/Program/Typed/Residual.lean
M src/Effect4/Laws/Program/Typed/Scheduler.lean
M src/Effect4/Laws/Program/Typed/Stack.lean
```

### f0591f36 — Retire the effectful-field Schema layer and its harness

25 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M .github/workflows/lean_action_ci.yml
M Makefile
M Test/All.lean
M Test/Audit/AxiomGate.lean
D Test/Codegen/EffectfulFieldContract.lean
M Test/Counterexamples/Archive/REGISTER.md
D Test/Counterexamples/Codegen/EffectfulField.lean
M Test/Counterexamples/REGISTER.md
D Test/Counterexamples/Schema/EffectfulField.lean
D Test/Counterexamples/Schema/EffectfulFieldProperties.lean
D Test/Schema/EffectfulFieldContract.lean
D Test/Schema/EffectfulFieldPropertiesContract.lean
D harness/schema-effectful-field/Generate.lean
D harness/schema-effectful-field/api.ts
D harness/schema-effectful-field/check.mjs
D harness/schema-effectful-field/check.sh
D harness/schema-effectful-field/floating.tail.ts
D harness/schema-effectful-field/missing-context.tail.ts
D harness/schema-effectful-field/missing-error.tail.ts
D harness/schema-effectful-field/positive.tail.ts
D harness/schema-effectful-field/tsconfig.json
D scripts/check-schema-effectful-field.sh
M src/Effect4.lean
D src/Effect4/Codegen/EffectfulField.lean
D src/Effect4/Schema/EffectfulField.lean
```

### d75f5c25 — Retire the obsolete Schema admission and image APIs

37 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M .github/workflows/lean_action_ci.yml
M Makefile
M Test/All.lean
M Test/Audit/AxiomGate.lean
M Test/Codegen/SchemaGenerationContract.lean
M Test/Codegen/SchemaGenerationCoverage.lean
M Test/Counterexamples/Archive/REGISTER.md
M Test/Counterexamples/REGISTER.md
D Test/Counterexamples/Schema/AnnotationDataPlane.lean
D Test/Counterexamples/Schema/CensusCoverage.lean
D Test/Counterexamples/Schema/Codec.lean
D Test/Counterexamples/Schema/KindAlphabetSeparation.lean
D Test/Counterexamples/Schema/NoLocalSymbolPropertyKey.lean
D Test/Counterexamples/Schema/NoNullLiteralKind.lean
D Test/Counterexamples/Schema/RecursiveElimination.lean
D Test/Counterexamples/Schema/SemanticTagSeparation.lean
D Test/Counterexamples/Schema/WireSpellingDrift.lean
M Test/Schema/AuthoringContract.lean
M Test/Schema/PayloadContract.lean
D harness/schema-annotations/EmitFieldAdmissionFixture.lean
D harness/schema-annotations/effect-annotations.ts
D harness/schema-annotations/tsconfig.json
M harness/schema-generation/EmitCoverageFixture.lean
M harness/schema-generation/EmitFixture.lean
D scripts/check-schema-annotations.sh
M src/Effect4.lean
M src/Effect4/Api.lean
M src/Effect4/Codegen/Schema.lean
M src/Effect4/Codegen/Target.lean
M src/Effect4/Laws.lean
D src/Effect4/Laws/Schema/Image.lean
D src/Effect4/Schema/Accepts.lean
M src/Effect4/Schema/Authoring.lean
D src/Effect4/Schema/Check.lean
M src/Effect4/Schema/Document.lean
D src/Effect4/Schema/Image.lean
M src/Effect4/Schema/Payload.lean
```

### 3d5ea883 — Trim Schema annotations to their retained carrier and keys

4 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M Test/Schema/AnnotationDataPlaneContract.lean
M src/Effect4/Codegen/Schema.lean
M src/Effect4/Schema/Annotations.lean
M src/Effect4/Schema/Document.lean
```

### 8cdc931b — Move shape rendering into the downstream Schema bridge

6 non-research paths. `A` adds, `M` modifies, `D` deletes.

```text
M Test/Schema/DialectContract.lean
M src/Effect4/Api.lean
M src/Effect4/Codegen/Schema.lean
A src/Effect4/Schema/OfShape.lean
M src/Effect4/Store/Domain/Canonical.lean
M src/Effect4/Store/Domain/Shape.lean
```
