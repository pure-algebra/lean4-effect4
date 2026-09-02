> Effect4-side status, 2026-09-02: the living Effect4 plan for this extraction is now [EFFECTS-SPLIT-PLAN](EFFECTS-SPLIT-PLAN.md), which names the package `Effects` and cuts the work into slices S0–S6. This copy is retained for the streams-side record and is not executed here.

> Copied from mepuka/lean4-WHATWG-streams at commit ed65fe0 on 2026-09-02 for the Effect4 side of the RS-D1 discussion. The streams repository holds the living copy; refine there or here, but say which is canonical when you do.

# Plan: extracting `Effect4.Algebra` into a standalone package (RS-D1)

Status: **PLAN ONLY, 2026-09-02. Nothing is executed.** The operator holds
this until incoming lean4-effect4 work on the Mac lands; the module facts
below were read from the local clone at commit `f4f55fa` and must be
re-read against whatever lands before any step runs.

Owner: the coordinator. Executing seat: to be named after the hold lifts.

## 1. What is being extracted

The nine modules of `Effect4/Algebra/` in lean4-effect4, read 2026-09-02:

| Module | Bytes | Imports (all internal to the tree) |
| --- | ---: | --- |
| `Effect4/Algebra/Signature.lean` | 819 | none |
| `Effect4/Algebra/MonadLaws.lean` | 1,295 | none |
| `Effect4/Algebra/Program.lean` | 1,700 | Signature |
| `Effect4/Algebra/Handler.lean` | 1,295 | Program |
| `Effect4/Algebra/Laws.lean` | 4,266 | Handler, MonadLaws |
| `Effect4/Algebra/Sum.lean` | 14,594 | Laws |
| `Effect4/Algebra/Universal.lean` | 10,612 | Sum |
| `Effect4/Algebra/Handler/Composition.lean` | 2,430 | Universal |
| `Effect4/Algebra/Handler/Category.lean` | 1,448 | Handler.Composition |

The tree imports nothing outside itself: no `Lean`, no Mathlib, no other
Effect4 area. Its only consumers are `Effect4/Schema/EffectfulField.lean`
(imports `Laws`) and the two algebra batteries plus their axiom report under
`Effect4Test/Algebra/`. Its contracts are `test/contracts/algebra-extraction.contract.md`
and `algebra-retained-closure.contract.md`; its counterexamples are the
eight `E4-ALG-CE-001`..`008` rows, three PINNED to Foldlab, five SEEDED in
the extraction battery. Its proof graph is closed in lean4-effect4's PLAN
("P3 algebra substrate: complete"), and the axiom receipts are inside
`propext`/`Quot.sound`.

That is the whole extraction surface: nine source modules, three test
modules, two contracts, eight register rows.

## 2. Target package

```text
lean4-effect-algebra/                 (new repository; name to be ruled)
  lakefile.toml                       name = "effectalgebra"; zero deps; leanOptions as here
  lean-toolchain                      leanprover/lean4:v4.33.1
  EffectAlgebra.lean                  root: imports the nine modules
  EffectAlgebra/
    Signature.lean  Program.lean  Handler.lean  MonadLaws.lean  Laws.lean
    Sum.lean  Universal.lean  Handler/Composition.lean  Handler/Category.lean
  EffectAlgebraTest.lean              root: batteries, axiom report, the gate
  EffectAlgebraTest/
    ExtractionContract.lean  RetainedClosureContract.lean  AxiomReport.lean
    Audit/AxiomGate.lean              the gate ported from this repository (tree names changed)
  Gates/ + bin/                       vendorseal is unnecessary (nothing vendored); citations and trustselftest are
  test/contracts/                     the two algebra contracts, moved
  test/counterexamples/REGISTER.md    the eight E4-ALG rows, renumbered EA-ALG-CE-001..008 with a mapping table
  test/fixtures/trust-gate/           known-red.txt and the plants
  docs/DESIGN-BASIS.md                DB-01 and DB-05 from lean4-effect4, verbatim with attribution
  docs/ALGEBRA-DAG.md                 the ten-edge graph, all edges carried over closed with receipts
  AGENTS.md and the boundary routers  the six-router shape from this repository
  LICENSE                             Apache-2.0
  .github/workflows/ci.yml            build, gates, leanchecker --fresh EffectAlgebraTest
```

Namespace: `EffectAlgebra` (the ruling asks: keep `Effect4.Algebra` as the
namespace to avoid touching consumers, or rename; default rename, with
lean4-effect4 keeping `Effect4.Algebra` as a re-export shim for one release).

## 3. Steps, in order, each with its check

| Step | Act | Check |
| --- | --- | --- |
| 0 | Re-read the nine modules and two batteries at the post-Mac commit; diff against `f4f55fa`; record the commit in this document | the import table above still holds; any new consumer of `Effect4.Algebra` is listed |
| 1 | Create the repository from this repository's P0 skeleton (routers, gates, CI, trust gate, citations gate) with the tree names changed | `lake build` green on the empty skeleton; trust self-test green |
| 2 | Move the nine modules by `git filter-repo` or `git subtree split` so history is preserved, then rename the namespace | `lake --wfail build` green; axiom gate reports the same declaration count as lean4-effect4's algebra battery counts |
| 3 | Move the two batteries and the axiom report; port the contracts and the eight register rows with a renumbering table | every battery green; every counterexample witness retained; `#print axioms` receipts identical to the source's |
| 4 | Dual-host build (Windows here, macOS at the operator's coordinator) and `leanchecker --fresh` | receipts parsed as `(declaration, axiom-set)` pairs, never raw lines |
| 5 | In lean4-effect4: add the pinned `[[require]]`, replace `Effect4/Algebra/*` by a re-export shim, delete the moved batteries, point the contracts at the new repository | lean4-effect4's full battery and trust gate green; its PLAN records the P12-style compatibility row |
| 6 | In this repository: nothing until P3 opens, then the dependency-policy acceptance probe from `PLAN.md` (exact pin, license, transitive cost) | `lake-manifest.json` gains exactly one package at an exact commit |
| 7 | Tag `v0.1.0` in the new repository; both consumers pin the tag's commit | both repositories build from a clean clone |

Steps 0 to 4 touch only the new repository. Step 5 is the first edit to
lean4-effect4 and is the one that waits on the Mac work. Step 6 waits on P3.

## 4. What must not change

- No definition body and no theorem statement in the nine modules changes
  during the move; a rename of the namespace is the only edit. Any needed
  change goes through the source repository's breaker process first.
- The eight counterexample witnesses move with their attacked statements.
- The axiom ceiling stays `propext` and `Quot.sound`; the package has no
  `Classical.choice` admission and no `Gates`-style tooling tree beyond the
  gate executables themselves.
- Zero dependencies. The package is the bottom of every tower in
  `docs/REIFICATION-STRATEGY.md`, so it may depend on nothing.

## 5. Rulings owed before step 1

| Id | Question | Default |
| --- | --- | --- |
| AP-1 | Repository name and namespace | `mepuka/lean4-effect-algebra`, namespace `EffectAlgebra` |
| AP-2 | History-preserving move or fresh copy with a provenance pin | history-preserving, so blame survives |
| AP-3 | Does lean4-effect4 keep a re-export shim, and for how long | one tagged release, then removed |
| AP-4 | Who is the executing seat and on which host | decided when the hold lifts |
| AP-5 | Does this repository take the dependency at P3 or vendor a pinned copy | dependency at an exact commit; vendoring only if the acceptance probe fails |
