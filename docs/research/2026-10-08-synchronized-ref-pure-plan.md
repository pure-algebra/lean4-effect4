# SynchronizedRef pure slice

The approved base is `08431c4e`.
The worktree branch is `codex/synchronized-ref-pure`.
The preserved branch is `codex/partitioned-core`.

## Interface and fragment

`Effect4.SynchronizedRef.handleTy A` declares the backing reference and the semaphore reference.
`make A initial` allocates both references and returns their record.
`get self` reads the backing reference directly.
`modify self body captures` runs a pure stored Step through Ref.modify under one semaphore permit.
The independent model remains `Effect4.Ref.Model`.
`buildingBlocks` records Ref and Semaphore.

Latest sources are `vendor/effect-4.0.1/src/SynchronizedRef.ts`: fields 38–42, construction 66–71, read 123, and modify 487–489.
The wrapper introduces no operation family or program representation.
Its result is the existing sole Eff syntax.
Effectful callbacks, set, waiting progress, cancellation agreement, and schedule agreement remain outside this slice.
G5 and G10 remain open.

The wrapper freezes self and every captured source at the caller's environment and path.
A local relocation inserts the wrapper's binders before a captured term's own binders.
The existing Step callback then inserts its current-value binder.
The public caller needs typing at its original scope, rather than stability under unknown wrapper locals.

## Ownership

Owned production paths are Library/SynchronizedRef/Cell.lean, Library/SynchronizedRef/Ops.lean, and Laws/Library/SynchronizedRef/Ops.lean under src/Effect4.
The owned battery is Test/Program/SynchronizedRef.lean.
This plan, the receipt, and the scoped audit are owned research paths.
The coordinator owns roots, registry, architecture, generated projections, and target execution.

## Proof placement

1. Concept: store-typing, required property R4, the checked types of composed library programs.
2. Question: compatibility readers of waiting-wrapper-typed, step-language-typed, and fold-typed-atomic-update.
   The existing claim pointers remain unchanged.
   make_answers, get_answers, and modify_answers consume those shared laws.
   Local relocation and record facts serve only these consumers.
3. Reach: nativeSignature, canonical formed A and B, typed caller sources, Step.Facts, and the checker's Answers judgment.
   The fragment has only make, get, and pure modify.
   Decisions 331, 333, and 335 bound latest sources, observations, and recorded building blocks.
4. Exclusions: typing proves no allocated identity, stored membership, lock ownership, waiting progress, schedule agreement, or host execution.
5. Unlock: R4 authoring clients construct checked Eff programs from the composed module.

The battery reads Ref.get_agrees and Ref.modify_callback_agrees at the actual pure body.
Those readers serve translation-simulation, ref-steps-agree, role simulation, R10.
Their reach remains one native backing step with the existing reading, value, and store premises.
They establish no whole-wrapper or schedule agreement.

## Finishing criteria

Build the law module and battery narrowly with LEAN_NUM_THREADS=3, one Lake process at a time.
Run actual programs and inspect replies, final backing values, and the released semaphore state.
Retain a source that would change its answer under wrapper locals as a capture control.
Reject malformed handles, wrong capture types, and wrong constructor inputs through public admission.
Read the existing Ref model laws at the actual body.
Audit compiled owned declarations against propext and Quot.sound.
Commit only the explicit owned paths after these controls pass.
