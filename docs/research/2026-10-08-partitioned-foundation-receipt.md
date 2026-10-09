# PartitionedSemaphore preparation and explanation-gate repair

The PartitionedSemaphore files are checked research probes, not a production module.
The next production slice covers scalar bookkeeping.
Its waiting and delivery model must retain partial reservations and synchronous client resumption.

## Base, branch, and ownership

Base: `8785c6f989f7b25df220649a238e93eda03921cb`.
Branch: `codex/partitioned-semaphore-plan`.
Read this receipt's head with `git log -1 --format=%H` after its explicit-path commit.
Worktree: `/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4`.
Claude lands S1a and S1b in the primary checkout during this review.
The final observed primary head is `979be0ad`.
Those new S1 commits are observed, not substantively reviewed in this slice.
The isolated checks keep the stated base.

## Scope

The [slice plan](2026-10-08-partitioned-semaphore-plan.md) orders production work and names its open obligations.
The [host packet receipt](2026-10-08-partitioned-semaphore-probes-receipt.md) retains finite Effect 4.0.1 observations.
The [authoring receipt](2026-10-08-partitioned-authoring-probe-receipt.md) retains the independent scalar model and its checked translations.
The [gate repair receipt](2026-10-08-explain-admission-receipt.md) records the separate proof-checking defect and its repair.

The preparation adds no library representation, registry claim, or owner ruling.
The scalar prototype uses the existing Step and Modeled declarations through the public entry modules.
The sole production change narrows the explanation tool's exception in `Test/Audit/AxiomGate.lean`.

## Independent replay

The following commands run in the integrating worktree.

```sh
sh docs/research/2026-10-08-partitioned-semaphore-probes/run.sh
```

The command exits zero and reproduces the retained output exactly.
It reports 22 positive observations and 10 rejected wrong-model predictions.
The packet checks Effect 4.0.1, Bun 1.4.2, and tsgo 7.0.0-dev.20260629.1.
Its selected input hashes agree with the retained inputs.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Author Effect4.Laws.Author ProofGraph.Audit ProofGraph.Axioms
```

The narrow build exits zero and reports 575 jobs.

```sh
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true -o docs/research/2026-10-08-partitioned-authoring-probe/Model.olean docs/research/2026-10-08-partitioned-authoring-probe/Model.lean
LEAN_NUM_THREADS=3 LEAN_PATH=. lake env lean -DwarningAsError=true -o docs/research/2026-10-08-partitioned-authoring-probe/Probe.olean docs/research/2026-10-08-partitioned-authoring-probe/Probe.lean
LEAN_NUM_THREADS=3 LEAN_PATH=. lake env lean -DwarningAsError=true docs/research/2026-10-08-partitioned-authoring-probe/Trust.lean
```

All three commands exit zero.
The positive readers, incorrect state controls, and wrong-field-type refusal pass.
The scoped audit checks 76 model and probe declarations.
The transitive axioms remain within `[propext, Quot.sound]`.
The replay leaves the original logs unchanged.

## Proof-gate replay

The repair replaces the whole-module exception with 24 exact reporting roots.
Their 17 measured descendants use the existing ancestor rule.
The 12 existing generated certificates keep the ordinary axiom ceiling.
The production diff changes no theorem, ancestor rule, or axiom-filter predicate.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Author.Explain Test.Audit.AxiomGate
python3 docs/research/2026-10-08-explain-admission-probe.py --label revised-mutant --policy revised --certificate mutant
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true --root=docs/research/2026-10-08-explain-admission-probe-fixture-mutant -o docs/research/2026-10-08-explain-admission-probe-fixture-mutant/Effect4/Laws/Author/Explain.olean docs/research/2026-10-08-explain-admission-probe-fixture-mutant/Effect4/Laws/Author/Explain.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-explain-admission-probe-revised-mutant.lean
python3 docs/research/2026-10-08-explain-admission-probe.py --label restored-clean --policy revised --certificate clean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true --root=docs/research/2026-10-08-explain-admission-probe-fixture-clean -o docs/research/2026-10-08-explain-admission-probe-fixture-clean/Effect4/Laws/Author/Explain.olean docs/research/2026-10-08-explain-admission-probe-fixture-clean/Effect4/Laws/Author/Explain.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-explain-admission-probe-restored-clean.lean
```

All commands exit zero.
The narrow build reports 265 jobs.
Both readers accept all 223 actual explanation declarations, including the reporting implementation.
The mutant reader verifies rejection of the added certificate's `Classical.choice` dependency.
The restored reader verifies acceptance of the same generated certificate without that dependency.
The generated sources and manifests reproduce without a tracked diff.

The retained old-policy source hash matches `git show 8785c6f9:Test/Audit/AxiomGate.lean`.
The revised source hash matches the current gate file.
The ancestor, admission-predicate, and axiom-filter block hashes remain equal across both policies.
The separate agent run retains old-policy acceptance of the same mutant.
The root independently reproduces the revised rejection and restored acceptance.

The private-policy extraction checks only admission and axiom filtering for the compiled module and fixture.
It does not execute the whole gate, private exception resolution, global staleness checks, or module closure.
The root separately checks that every new exact reporting root appears in the measured choice-reaching declarations.

## Authoring result

The author declares the scalar record once.
Deriving supplies its schema, carrier conversions, and inverse laws.
Named fields and contexts feed stored steps and their generated source applications.
Shared laws supply reading and typing under their stated premises.
Independent model equations describe the desired reply and scalar record.

The next mechanical improvement packs carrier values from the existing named context declaration.
Proof callers currently repeat positional tuples.
That improvement needs no second program representation or metadata list.
It does not replace independent behavior specifications.

## Final checks

```sh
python3 scripts/check-language.py --strict docs/research/2026-10-08-partitioned-semaphore-plan.md docs/research/2026-10-08-partitioned-foundation-receipt.md
git diff --check
```

The selected Markdown files and whitespace check pass.
The change inventory contains only the named research packets and `Test/Audit/AxiomGate.lean`.

## Checkpoint and limits

REF-REG-01 is resolved in `8785c6f9`; its claim now states the reply and final-store observation.
The C3 and C4 source review checks import direction, semantics registry relocation, and the acceptance import fence at the stated base.
The C3 explanation exception receives the separate repair described above.
The narrow public-entry build checks the prototype's actual authoring imports.
No full module-closure or whole-library axiom gate runs.

The host packet establishes finite observations under its selected runtime and scheduler.
The scalar laws establish translation, reading, and typing for their exact inputs and premises.
They establish no whole-module simulation, fairness, progress, codec admission, or request-handle allocation.
Cancellation after selection remains conditional source evidence without a deterministic host reproduction.
Whole cells containing actual waiter identities remain outside current Modeled derivation.
G1, G5, G9, G10, and the later delivery contract remain open.
The production scalar slice still needs its concrete claim placement before its helpers move into the library.

No merge, push, full sweep, production PartitionedSemaphore implementation, or Claude-session message occurs.
