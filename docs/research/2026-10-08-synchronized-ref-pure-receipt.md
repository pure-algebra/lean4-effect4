# SynchronizedRef pure receipt

The coordinator must add the two core imports, the law import, and the battery import before the library and module closure gates apply.
No wrapper agreement claim lands.
G5 and G10 remain open.

## Commits and ownership

Base: `08431c4e81c5f48be2ae8ba810e4fecad8c58139`.
Production head: `760b5d14ffec3e37b9c53c55f1c7a56358f1f6eb`.
Branch: `codex/synchronized-ref-pure`.
Worktree: `/Users/pooks/.codex/worktrees/module-folds/lean4-effect4`.
The preserved `codex/partitioned-core` branch remains at `a6d3199e8e7152434cc781911fba1ffd2bb891c5`.
The primary checkout receives no edit or build.

Changed paths:

- `src/Effect4/Library/SynchronizedRef/Cell.lean`
- `src/Effect4/Library/SynchronizedRef/Ops.lean`
- `src/Effect4/Laws/Library/SynchronizedRef/Ops.lean`
- `Test/Program/SynchronizedRef.lean`
- `docs/research/2026-10-08-synchronized-ref-pure-plan.md`
- `docs/research/2026-10-08-synchronized-ref-pure-audit.lean`
- This receipt.

The coordinator retains roots, registry, architecture, generated output, and target execution.
No lakefile, rulings, owner document, or existing source changes.

## Landed interface

`Effect4.SynchronizedRef.handleFields` and `handleTy` retain the backing value type in a required record of two reference handles.
`buildingBlocks` records Ref and Semaphore as concrete data.
`make` allocates the backing reference and a one-permit semaphore.
`get` reads the backing reference directly.
`modify` supplies a pure stored Step to Ref.modify inside Semaphore.withPermits.
`relocate` and `freeze` are local source helpers.
They resolve self and captured sources at the original environment and path.
They relocate captured internal binders past wrapper locals.
The existing Step.callback adds its current-value binder afterward.

The independent value model is the unchanged `Effect4.Ref.Model` in `src/Effect4/Library/Ref/Model.lean`.
The core emits existing Eff forms only.
Latest sources are `vendor/effect-4.0.1/src/SynchronizedRef.ts`: fields 38–42, construction 66–71, get 123, and modify 487–489.

## Proof placement

1. Concept: store-typing, required property R4, typing of composed library programs through the existing checker.
2. Question: compatibility readers of waiting-wrapper-typed, step-language-typed, and fold-typed-atomic-update.
   Existing registry pointers remain unchanged.
   No new claim or planned goal is introduced.
3. Reach: Answers at nativeSignature for make, get, and pure modify.
   Premises retain canonical formed A and B, typed caller sources, and Step.Facts.
   Decisions 331, 333, and 335 bound the latest source, observations, and recorded building blocks.
4. Exclusions: typing does not establish allocation identities, stored membership, lock ownership, waiting progress, schedule agreement, or host execution.
5. Unlock: R4 clients author checked programs through the same Eff interface.

All landed theorems live in `src/Effect4/Laws/Library/SynchronizedRef/Ops.lean`.
The following table places each theorem on its real consumer path.

| Theorem | Consumer |
| --- | --- |
| `Effect4.SynchronizedRef.relocate_types` | `freeze_kept`, through the existing `argTy_weaken` |
| `Effect4.SynchronizedRef.reached_slots` | `freeze_kept`, at each reached wrapper scope |
| `Effect4.SynchronizedRef.freeze_kept` | `modify_answers`, for self and every captured source |
| `Effect4.SynchronizedRef.handle_normal` | `make_answers`, `backing_type`, and `semaphore_type` |
| `Effect4.SynchronizedRef.handle_nodes` | `make_answers`, through the declared-record construction law |
| `Effect4.SynchronizedRef.backing_type` | `get_answers` and `modify_answers` |
| `Effect4.SynchronizedRef.semaphore_type` | `modify_answers` |
| `Effect4.SynchronizedRef.make_answers` | The public constructor reader in the battery |
| `Effect4.SynchronizedRef.get_answers` | The numeric public read reader in the battery |
| `Effect4.SynchronizedRef.modify_answers` | The actual numeric callback reader in the battery |

The shared laws consumed are answers_bindWith, answers_refMake, types_record_declared, answers_refGet, Ref.modify_callback_answers, and Semaphore.withPermits_types.
The capture proof consumes argTy_weaken and the existing TypedScope.Reaches judgment.

The two model readers serve translation-simulation, ref-steps-agree, role simulation, R10.
They apply Ref.get_agrees and Ref.modify_callback_agrees to the actual numeric transition.
Their observation contains the reply and final stores of one allocated backing operation.
They retain the existing image, reading, callback value, and held-cell premises.
They establish no whole-wrapper or schedule agreement.
They provide an R10 client of the shared model connectors, while G10 stays open.

## Verification

All Lake commands run in the assigned worktree with LEAN_NUM_THREADS=3, one process at a time.
Initial narrow builds exposed Lean namespace, field-order, and indexed-carrier annotation errors.
Those errors are repaired before the successful commands below.

- `LEAN_NUM_THREADS=3 lake build Test.Program.SynchronizedRef` passes: 947 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Program.SynchronizedRef ProofGraph.Audit ProofGraph.Axioms` passes: 947 jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-synchronized-ref-pure-audit.lean` passes.
- `git diff --cached --check` passes before the production commit.
- `git diff HEAD^ HEAD --check` passes after the production commit.
- `rg -c '^#guard' Test/Program/SynchronizedRef.lean` reports 16 controls.
- `rg -c '^example' Test/Program/SynchronizedRef.lean` reports five readers.

The finite programs check numeric, string, and allocated deferred-handle values.
The numeric transition returns the old value and adds the captured amount to the backing value.
Each observed modify finishes with permits 1, taken 0, no waiters, and next stamp 0.
The constructor/read observation retains the unchanged backing value.
The constructor's inferred type equals handleTy nat.

The controls retain caller names current and acc.
Scope-depth-sensitive self and capture sources succeed after freezing.
The otherwise identical unfrozen composition is refused by admission.
A capture with its own fold reads its original item after both wrapper and callback relocation.
Wrong constructor values, malformed handles, and wrong capture types are refused.
A refusing capture retains its original caller path and reason.

These are finite machine evaluations under Api.run's evaluate-and-flush tape and fuel 2000.
They establish neither universal scheduling nor TypeScript execution.
No sweep or independent-review claim is made.

## Compiled trust and imports

The retained audit checks 57 compiled owned declarations, including the battery.
It refuses unsafe, partial, axiomatic, external, replaced, and bodiless declarations.
It checks reached axioms against propext and Quot.sound.
All declarations pass.
The three public typing laws reach exactly propext and Quot.sound.
The core import closure reaches no Effect4.Laws module.
The reused Ref.Model import closure reaches no Step or Laws module.

## Authoring burdens and boundaries

Canonical record order, normal forms, formed nodes, and field declarations remain separate proof inputs.
The existing declared-record construction law handles the common record proof.
The local handle facts connect that shared law to the two fields.

Wrapper captures need arbitrary-slot relocation before the existing one-slot callback connector.
This slice records the actual consumer and keeps that helper local.
A future shared capture helper could combine original-path resolution, relocation, and a Kept connector.
Such a helper should retain refusal paths and internal-fold controls.

The model reader still writes the carrier pair `(amount, ())` explicitly.
The coordinator's proposed input_values command could remove this repeated positional burden.
This branch does not depend on that command.
Indexed carrier callbacks also require an explicit Nat annotation at the independent transition.

Set and effectful callbacks remain outside the interface.
No whole-wrapper, cancellation, waiting-progress, lock-ownership, target, or host theorem is added.
G5 and G10 remain open.
