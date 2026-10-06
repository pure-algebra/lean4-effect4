# Adversarial review of the saved-mask pop candidates

Status: source review complete; the statements remain uncompiled.
Source: frozen main `818a73ce`. The original candidate and receipt remain unchanged.

## Result

No counterexample appears to the exact `popFrom_maskChain` or `getCont_maskChain` statement.
The empty detached scratch-stack premise is essential.
No extra restriction on demand, skip, causes, deferred interrupts, or frame membership appears necessary.
Lean checking must still establish the proposed statements.

Completion criteria cover every flag-changing hook, both stopping paths, recursive continuation, and the deferred-interrupt branch.
This review reads definitions and existing equations. It executes no program, model, compiler, build, or proof.

## Exhaustive source cases

The induction follows `FrameFiber.popFrom` in `src/Effect4/Machine/Frames.lean`.
`Prim.ensure` has three relevant behaviours.

| Hook case | Direct answer | Continued pop |
| --- | --- | --- |
| Neutral hook | The bit stays unchanged. Appending the untouched remainder satisfies its original chain. | Empty scratch survives `passPushed`; the induction applies to the remainder. |
| `setInterruptible saved` | The input chain supplies the remainder's relation at `saved`. The hook sets that bit before returning. | Scratch stays empty. The induction applies to the remainder at `saved`. |
| Masking `onExit` or `asyncFinalizer` | The hook changes true to false and pushes `setInterruptible true`. Appending the remainder satisfies the original base. | `passPushed` restores true and empties scratch. The remainder has its original relation. |

A masking hook that does not push is neutral for both the stack and bit.
A pushed frame can itself answer or be skipped.
`FrameFiber.joinPushed` either returns the recursive result or appends the original remainder to the post-push result.
Both paths therefore retain the same base-indexed relation.

The recursive call receives empty scratch in every case.
This establishes the induction's required premise without strengthening the candidate.
`FrameFiber.passOn` changes trace fields only; its returned fiber is the tail's fiber.

## Arbitrary inputs and stop boundaries

`Prim.answerOf` returns answer data. It does not mutate the fiber.
A pending cause may replace the answer when a restoring frame enables interruption.
The hook still restores the saved bit and preserves its scratch stack.
Skipping the replacement or stopping there both satisfy the same chain relation.

The carried cause is separate from the fiber's pending cause.
Existing `FrameFiber.popFrom_fiber_cause` already removes the carried-cause parameter from the returned-fiber equality.
Neither cause needs a well-formedness premise for this observation.

`Arm.contAll` needs no exclusion.
A restoring frame may answer that demand, after its hook sets the saved bit.
A finalizer may answer while retaining its newly pushed restoring frame.
Both direct stops preserve the relation.

An arbitrary primitive lacking an arm is a neutral passed entry unless it has a specified hook.
Nested bodies, finalizer names, current instructions, and values are not executed by this traversal.
No `Prim.isFrame` premise is needed for the proposed stack observation.

`FrameFiber.getCont` either clears only `deferredInterrupt`, or detaches the actual stack into `popFrom` with empty scratch.
Its early branch preserves the bit and stack unchanged.
The main helper applies directly to its other branch.
`Machine.frameExitState` selects between two such calls, so its adapter needs no new premise.

## Premise-removal witness

Remove `scratchEmpty` and choose `frames = []`, `base = false`, and `f.interruptible = false`.
Let the detached scratch stack instead contain `[Prim.setInterruptible true]`.
The input premise `MaskChain false false []` holds.
`popFrom` returns `f` unchanged in its empty-frames branch.
The output relation then requires `MaskChain false true []`, which requires `true = false`.

This is a constructed source-reduction witness against the weakened statement.
It is not an executed probe or a reachable-machine counterexample.
The exact candidate already excludes it.

## Proof-route caution and limits

`FrameFiber.ensure_stack_cases` alone does not establish flag preservation in its unchanged-stack alternative.
A restoring frame changes the flag without changing scratch.
Keep its case separate and reuse `Prim.ensure_setInterruptible_flag` and `Prim.ensure_setInterruptible_stack`.
The candidate's statement requires no repair.

Placement remains the proposed R11 helper for `scope-lifetime-finalization`, serving the future run-level saved-mask relation.
The consumer remains Waiting and protected Semaphore execution after their machine-preservation obligations.
No whole-run, completed-exit, cleanup multiplicity, notification, budget, liveness, or host agreement claim follows here.
The previously recorded arbitrary `exitDone` trap still constrains that later lift.
