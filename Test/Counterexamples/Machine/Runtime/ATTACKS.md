# Runtime scope attacks

These attacks belong to the `Effect4.Scope` first-order state-machine packet
frozen by [`test/contracts/scope.contract.md`](../../contracts/scope.contract.md)
and [`docs/SCOPE-DAG.md`](../../../docs/SCOPE-DAG.md). Stable IDs live in
[`../REGISTER.md`](../REGISTER.md); the executable Lean witnesses live in
`Effect4Test/Counterexamples/Runtime/Scope.lean` and are a self-contained
breaker model that stays green while the production surface is absent.

The `E4-RUN-CE-*` family is new with this packet and is the runtime area's
first. Its token follows the register's existing derivation: a directory name
of six characters or fewer becomes the family verbatim (`data`, `flow`,
`schema`, `target`), and a longer one is abbreviated to its first three or four
letters (`algebra` to `ALG`, `semantics` to `SEM`, `environment` to `ENV`,
`concurrency` to `CONC`). `runtime` is seven characters, so it abbreviates to
`RUN`.

The pinned source is `effect@4.0.0-rc.112` under
`vendor/effect-4.0.0-rc.112/src/`, read in
`docs/effect-rc112-fiber-runtime.html` section 6.

## E4-RUN-CE-001 — close runs finalizers before writing the state

- **BROKE:** `scopeCloseUnsafe` may run its finalizers and then record the
  scope as `Closed`, because the two orders differ only in an unobservable
  intermediate.
- **WITNESS:** `close_must_write_state_first` — a finalizer that registers
  another finalizer during the close sees a `Closed` scope under the pinned
  order, so its registration runs immediately with the closing exit; under the
  rejected order it sees an `Open` scope, reports success without running
  anything, and is recorded in a scope that is about to be discarded.
  `close_state_is_independent_of_finalizers` — the state the close writes
  carries no finalizer result and no registration list.
- **CLASS:** lost finalizer, observable intermediate state.
- **FIXED-BY:** `Scope.closeState` takes no `run` argument at all, so
  `Scope.close_state_independent_of_run` holds by construction;
  `Scope.close_reentrant_add` states what a re-entrant finalizer observes, and
  `Scope.closeState_finalizers` empties the registration list. Census rows
  `scope.close-state-first`, `rule.scope-close-lifo-state-first`.

## E4-RUN-CE-002 — finalizers run in registration order

- **BROKE:** a scope may run its finalizers in the order they were registered.
- **WITNESS:** `close_order_is_lifo` — three registrations close as `[2, 1, 0]`
  under the pinned order and `[0, 1, 2]` under the rejected one.
  `close_order_changes_the_cause` — the two orders produce different flat
  closing causes, so the difference is observable in the exit and not only in
  the sequence of calls.
- **CLASS:** wrong finalization order.
- **FIXED-BY:** `Scope.closeOrder_eq` reverses the materialised list,
  `Scope.closeOrder_last_first` states that whatever was registered last is the
  head, and `Scope.closeExits_reverse` is the backwards
  `Array.from(finalizers.values())` loop. Census row `scope.close-lifo`.

## E4-RUN-CE-003 — close is not idempotent

- **BROKE:** closing a scope twice may re-run its finalizers, or may overwrite
  the stored closing exit with the second one.
- **WITNESS:** `close_is_idempotent` — the pinned close returns the
  already-`Closed` scope untouched with the first exit, while a close without
  the `Closed` guard replaces the stored exit with the second one.
  `close_guard_prevents_double_run` — the guard is what makes the second close
  run no finalizer.
- **CLASS:** repeated finalization, lost exit.
- **FIXED-BY:** `Scope.close_idempotent`, `Scope.close_twice`,
  `Scope.closeState_idempotent`, and `Scope.closeResult_closed`. Census row
  `scope.close-state-first`.

## E4-RUN-CE-004 — adding a finalizer to a Closed scope

- **BROKE:** `scopeAddFinalizerExit` on a `Closed` scope may register the
  finalizer like any other, or may silently drop it.
- **WITNESS:** `add_after_closed_runs_now` — the pinned add returns the
  finalizer's own exit, run against the stored closing exit; both rejected
  variants report success and never run the finalizer at all.
  `add_after_closed_registers_nothing` — `scopeAddFinalizerUnsafe` has no
  `Closed` arm, so the registration list of a `Closed` scope never grows.
- **CLASS:** leaked resource, dropped finalizer.
- **FIXED-BY:** `Scope.addExit_closed`,
  `Scope.addExit_closed_registers_nothing`, and `Scope.addUnsafe_closed`.
  `Scope.acquireRelease_closed_ambient` carries the same behaviour to the
  bracket. Census row `scope.add-after-closed`.

## E4-RUN-CE-005 — removal normalises, and the cleared inline slot

- **BROKE:** removal may normalise every scope into a keyed map first, and a
  cleared inline slot is just the empty map.
- **WITNESS:** `remove_leaves_non_open_untouched` — a normalising removal turns
  `Empty` into an `Open` scope that would then accept registrations, and turns a
  `Closed` scope back into an `Open` one, losing the stored exit.
  `cleared_inline_slot_is_its_own_state` — `openEmpty`, `empty`, and
  `openMap []` are three distinct states, and the difference is observable at
  the very next add: a cleared inline slot takes it inline again, an emptied map
  takes it into the map. `remove_inline_miss_is_a_no_op` — an inline slot under
  a different key is untouched, because in that shape there is no map to delete
  from.
- **CLASS:** resurrected scope, collapsed state.
- **FIXED-BY:** `Scope.removeUnsafe_not_open`,
  `Scope.removeUnsafe_inline_hit`, `Scope.removeUnsafe_inline_miss`,
  `Scope.removeUnsafe_openMap`, `ScopeState.openEmpty_ne_openMap_nil`, and
  `Scope.addUnsafe_openEmpty`. Census rows `scope.remove-finalizer`,
  `scope.states`.

## E4-RUN-CE-006 — a child of a Closed parent

- **BROKE:** `scopeForkUnsafe` always returns a fresh `Empty` child.
- **WITNESS:** `fork_of_closed_parent_is_born_closed` — with a `Closed` parent
  the pinned fork returns a child that is already `Closed` with the parent's
  exit, while the rejected fork returns an `Open` child that accepts a
  registration no close will ever run, and adds a finalizer to a parent that has
  already finished closing.
- **CLASS:** leaked resource, lost exit.
- **FIXED-BY:** `Scope.fork_closed_parent` and
  `Scope.fork_closed_parent_child_exit` return the parent untouched and hand the
  child the parent's exit, so anything registered on it afterwards runs
  immediately through `Scope.addExit_closed`. Census row `scope.fork-linkage`.

## E4-RUN-CE-007 — the fork link uses two keys

- **BROKE:** the parent-side finalizer and the child-side finalizer may each
  mint their own key, since each is registered on a different scope.
- **WITNESS:** `fork_link_needs_one_shared_key` — with one key, removing it
  restores the parent's registration list exactly; with two, the child's
  removal misses and the parent keeps a finalizer that closes an
  already-closed child. `fork_registers_the_same_key_on_both_sides` — both
  sides really do carry the same key.
- **CLASS:** leaked finalizer.
- **FIXED-BY:** `Scope.fork` takes one `key` and registers it on both sides;
  `Scope.fork_shared_key` and `Scope.fork_detach` are the two halves of the
  linkage. Census row `scope.fork-linkage`.

## E4-RUN-CE-008 — a failing finalizer aborts the close

- **BROKE:** the sequential strategy may stop at the first finalizer that
  fails.
- **WITNESS:** `sequential_close_captures_failures` — with a failure at the head
  of the close order the short-circuiting variant produces one exit where the
  pinned loop produces three, so the finalizers registered *before* the failing
  one never run. `short_circuit_loses_a_reason` — the dropped failure is
  dropped from the closing cause as well, so the difference is observable in
  the exit.
- **CLASS:** skipped finalization, lost reason.
- **FIXED-BY:** `Scope.closeExits` is a total `map`, so
  `Scope.closeExits_length` states that every registered finalizer contributes
  an exit and `Scope.closeResult_reasons` states that every failure reaches the
  closing cause. That is the modelled half of `exit()`-capture; the temporal
  "awaited" half needs the fiber machine, and `docs/SCOPE-DAG.md` keeps the row
  `partial` for it. Census row `scope.close-sequential`.

## E4-RUN-CE-009 — close always merges through exitAsVoidAll

- **BROKE:** `scopeCloseUnsafe` merges its finalizer exits through
  `exitAsVoidAll` in every case.
- **WITNESS:** `single_finalizer_is_not_merged` — rc.112 short-circuits at
  `finalizers.size === 1` and returns that finalizer's effect directly, so a
  single finalizer failing with an empty cause fails the close, while the merge
  would have succeeded. `many_finalizers_are_merged_flat` — with two or more the
  two agree, and every failure reason is concatenated into one flat cause in
  close order. `merge_is_concatenation_not_union` — the merge keeps duplicates,
  so it is `exitAsVoidAll` and not `causeCombine`.
- **CLASS:** wrong result arm, erased failure.
- **FIXED-BY:** `Scope.closeResult` keeps three arms —
  `Scope.closeResult_nil`, `Scope.closeResult_single`, `Scope.closeResult_many`
  — with `Scope.closeResult_reasons` tying all three to one flat reason list.
  The empty-cause case rests on the already-proved
  `Exit.asVoidAll_empty_cause` from the Cause/Exit packet. Census rows
  `scope.close-merge`, `scope.close-parallel`.

## Frame-machine attacks

The attacks below belong to the frame-machine packet frozen by
[`test/contracts/frames.contract.md`](../../contracts/frames.contract.md) and
[`docs/FRAMES-DAG.md`](../../../docs/FRAMES-DAG.md). Their executable Lean
witnesses live in `Effect4Test/Counterexamples/Runtime/Frames.lean` and are a
second self-contained breaker model, independent of the scope one above.

The pinned source is `effect@4.0.0-rc.112` under
`vendor/effect-4.0.0-rc.112/src/`, read in
`docs/effect-rc112-fiber-runtime.html` sections 1-4.

## E4-RUN-CE-010 — contAll runs only on the answering frame

- **BROKE:** `getCont` may run a frame's `contAll` only when that frame answers
  the demanded arm, because a frame that does not answer "was not used".
- **WITNESS:** `contAll_runs_on_skipped_frames` — with a mask frame below a user
  `catchCause` handler, the pinned pop clears the interruptible flag on the way
  past and the rejected pop leaves it set, so the finalizers and handlers above
  run in the wrong mask. `contAll_skipped_frame_is_still_popped` — both pops
  traverse the same frames, so the difference is the hook and not the traversal.
- **CLASS:** lost mask, wrong interruptibility.
- **FIXED-BY:** `Prim.ensure` is applied to every frame `Prim.answerOf` is asked
  about; `FrameFiber.popFrom_ranContAll` and `FrameFiber.getCont_ranContAll`
  state that every popped frame declaring `contAll` leaves a `ranContAll` event.
  Census row `rule.frames-are-primitives`.

## E4-RUN-CE-011 — a user error handler catches an interrupt

- **BROKE:** `exitFailCause` pops one `contE` frame and calls it, so
  `catchCause` sees an interruption like any other cause.
- **WITNESS:** `interrupt_skips_user_handlers` — with the fiber interruptible
  and a cause recorded, the pinned pop discards the handler and empties the
  stack, while a pop without the skip hands the interrupt to the handler, which
  recovers from it. `skip_requires_a_pending_cause` — with no interruption
  recorded the same handler answers, so the skip is conditional and not a
  blanket refusal to pop.
- **CLASS:** swallowed interruption, uninterruptible fiber.
- **FIXED-BY:** `FrameFiber.resumeCause` demands `contE` with
  `skipInterrupted := true`, and `FrameFiber.interrupt_skips_every_handler`
  states that with no mask frame on the stack the pop empties it. Census rows
  `checkpoint.exit-failcause-skip`, `rule.interrupt-bypasses-handlers`,
  `op.Failure`.

## E4-RUN-CE-012 — the skip is decided once, before the loop

- **BROKE:** the skip condition may be read once, when the failure starts
  travelling, rather than after every `contAll`.
- **WITNESS:** `mask_frame_stops_the_skip` — with a `SetInterruptible(false)`
  frame below the handler, the pinned pop clears the flag on the way past and
  the handler inside the uninterruptible region does run, while a pop that
  decided the skip up front discards it and empties the stack.
- **CLASS:** skipped finalization, lost recovery.
- **FIXED-BY:** the skip test in `FrameFiber.popFrom` reads
  `(frame.ensure fiber).fst.interrupted`, the flag *after* the hook;
  `FrameFiber.getCont_mask_stops_skip` is the law. Census row
  `rule.interrupt-bypasses-handlers`.

## E4-RUN-CE-013 — SetInterruptible only restores the flag

- **BROKE:** a `SetInterruptible` frame's `contAll` may only assign the flag,
  since restoring interruptibility is all the combinator promises.
- **WITNESS:** `set_interruptible_substitutes_with_a_pending_cause` — popping
  `SetInterruptible(true)` with a cause already recorded returns
  `failCause(cause)` as the continuation for either arm under the pinned hook,
  while the flag-only hook lets the success value continue into the `flatMap`
  above and loses the interruption entirely.
  `set_interruptible_without_a_cause_substitutes_nothing` — with no cause the
  same frame substitutes nothing, so the substitution is conditional.
- **CLASS:** lost interruption, resumed after cancellation.
- **FIXED-BY:** `Prim.ensure_setInterruptible_substitutes`,
  `Prim.answerOf_replacement`, `FrameFiber.resumeValue_replacement` and
  `FrameFiber.resumeCause_replacement`. Census rows
  `checkpoint.set-interruptible-contall`, `frame-arm.SetInterruptible`,
  `op.SetInterruptible`.

## E4-RUN-CE-014 — the OnExit finalizer runs unmasked

- **BROKE:** an `OnExit` frame's `contAll` may leave the flag alone, because the
  finalizer is "just another effect".
- **WITNESS:** `on_exit_finalizer_runs_masked` — the pinned hook clears the flag
  and pushes `SetInterruptible(true)`, so the finalizer runs uninterruptibly and
  interruptibility comes back afterwards; the rejected hook leaves the finalizer
  interruptible and pushes nothing, so an interrupt arriving during cleanup
  abandons it. `on_exit_told_not_to_mask` — `acquireUseRelease` passes `true` and
  then the hook really does nothing, so the mask is not unconditional.
- **CLASS:** abandoned finalizer, leaked resource.
- **FIXED-BY:** `Prim.ensure_onExit_masks`, `Prim.ensure_onExit_told_not_to` and
  `Prim.ensure_onExit_already_masked`. Census rows `frame-arm.OnExit`,
  `op.OnExit`, `scope.scoped`.

## E4-RUN-CE-015 — the OnExit arm returns the finalizer's exit

- **BROKE:** either `OnExit` arm may return whatever the finalizer produced,
  since that is the last thing that ran.
- **WITNESS:** `on_exit_restores_the_original_exit` — a successful finalizer must
  leave the original exit alone; an arm that returns the finalizer's exit
  replaces the computation's result with the finalizer's, which for a void
  finalizer means every `ensuring` erases its subject's value.
- **CLASS:** lost result.
- **FIXED-BY:** both arms go through `Effect4.Exit.restoreAfterFinalizer`;
  `Prim.armA_onExit`, `Prim.armE_onExit` and
  `Prim.onExit_finalizer_success_restores` are the laws. Census row `op.OnExit`.

## E4-RUN-CE-016 — a failing finalizer keeps one cause

- **BROKE:** when both the computation and its finalizer fail, one of the two
  causes may be kept and the other dropped.
- **WITNESS:** `finalizer_failure_merges_by_combine` — the pinned arm merges both
  by `causeCombine`, while keeping only the original loses the finalizer's
  failure and keeping only the finalizer's loses the original.
  `finalizer_failure_under_success_stands_alone` — under a *successful* exit the
  finalizer's failure is the whole result, because `combineFinalizerCause` only
  combines on the failure arm.
- **CLASS:** erased failure.
- **FIXED-BY:** `Prim.onExit_finalizer_failure_merges` and
  `Prim.onExit_success_finalizer_failure`, both stated over the already-proved
  `Effect4.Exit.restoreAfterFinalizer_failure_failure` and
  `restoreAfterFinalizer_success_failure`. Census rows `op.OnExit`,
  `frame-arm.OnExit`.

## E4-RUN-CE-017 — the arms are fixed by the op

- **BROKE:** the continuation arms may live on the op prototype, the way
  `evaluate` does, so every `OnSuccess` frame answers the same way.
- **WITNESS:** `arms_are_assigned_per_instance` — two `flatMap` frames differing
  only in their stored continuation must behave differently, and a
  prototype-level `contA` collapses them into one.
  `the_three_frames_answer_different_arms` — `OnSuccess` answers `contA` only,
  `OnFailure` answers `contE` only, and `OnSuccessAndFailure` answers both, so
  the matrix is per-op while the arms' contents are per-instance.
- **CLASS:** collapsed continuation, wrong handler.
- **FIXED-BY:** `Prim.onSuccess` and `Prim.onFailure` store a continuation name
  per frame; `Prim.onSuccess_arm_is_per_instance`,
  `Prim.onFailure_arm_is_per_instance` and
  `Prim.onSuccessAndFailure_arms_are_per_instance` are the laws, and
  `Prim.armA_isSome`/`armE_isSome` tie the matrix to the arms. Census rows
  `op.OnSuccess`, `op.OnFailure`, `op.OnSuccessAndFailure`, and the three
  matching `frame-arm.*` rows.

## E4-RUN-CE-018 — a generator's Exit travels through the stack

- **BROKE:** an `Exit` a generator yields may be returned as the next primitive
  like any other effect, since an Exit is a primitive.
- **WITNESS:** `iterator_folds_exits_inline` — the pinned arm consumes the whole
  inline run of `Success` exits within one `contA` call and reaches its result in
  a single machine step, while routing each folded exit through the stack costs
  one step and one `getCont` per value. The count is observable because every
  `getCont` is a checkpoint at which a deferred interrupt is noticed, so the
  rejected model can be interrupted in the middle of a `gen` block that the
  pinned one runs atomically. `iterator_pushes_only_for_a_real_effect` — the
  frame is pushed only when the generator yields a non-Exit effect.
- **CLASS:** spurious interruption point, wrong step count.
- **FIXED-BY:** `PrimInterp.iterNext` supplies the maximal inline run as
  first-order data, and `Prim.iterator_folds_inline` states that the arm depends
  only on the outcome that ended it. `Prim.armA_iterator_done`,
  `armA_iterator_halt` and `armA_iterator_resume` are the three arms. Census
  rows `op.Iterator`, `frame-arm.Iterator`.

## E4-RUN-CE-019 — While runs the body again without re-testing

- **BROKE:** `While`'s `contA` may step the cursor and run the body again,
  because `evaluate` already checked the predicate.
- **WITNESS:** `while_retests_through_contA` — at the cursor where the predicate
  goes false the pinned arm stops and the rejected arm pushes the frame again,
  so the loop never ends. `while_steps_before_it_retests` — below the bound both
  agree, so the difference is the re-test and not the step.
- **CLASS:** non-terminating loop, off-by-one iteration.
- **FIXED-BY:** `Prim.armA_whileLoop_continue` and `Prim.armA_whileLoop_stop`
  step first and test the *stepped* cursor. Census rows `op.While`,
  `frame-arm.While`.

## E4-RUN-CE-020 — an empty stack drops the value

- **BROKE:** producing a value with nothing left to pop may be a defect, or the
  value may simply be dropped in favour of a canonical void exit.
- **WITNESS:** `empty_stack_yields_the_exit` — the fiber must yield the Exit it
  produced; replacing it with a defect loses the result of every top-level
  computation. `empty_stack_yields_a_failure_unchanged` — a failure with nothing
  to catch it is yielded unchanged, not wrapped.
- **CLASS:** lost result, fabricated defect.
- **FIXED-BY:** `FrameFiber.resumeValue_empty`, `FrameFiber.resumeCause_empty`
  and `FrameFiber.step_ofExit_finishes`. Census rows `op.Success`, `op.Failure`,
  `exit.success-failure`.

## E4-RUN-CE-021 — the two foreign boundaries can be modelled

- **BROKE:** `withFiber` and `YieldableError` may be given behavioural models,
  because the first "just returns an effect" and the second "just fails".
- **WITNESS:** `with_fiber_cannot_see_the_raw_fiber` — two host fibers agreeing
  on the five modelled fields and differing in their observer list and child set
  are one Effect4 value, so no Effect4 interpretation can distinguish them,
  while rc.112 hands the callback the object that carries both.
  `yieldable_error_cannot_see_the_host_class` — two host `Error`s with equal
  Effect4 payloads and different messages and stacks are one Effect4 cause, while
  rc.112's `exitFail(this)` fails with the object itself.
  `yieldable_error_evaluates_to_its_own_failure` — the behaviour behind the
  boundary is still modelled; only the identity is refused.
- **CLASS:** overclaimed model, unrepresentable host identity.
- **FIXED-BY:** `Prim.withFiber_refused` and
  `Prim.yieldableError_host_class_refused` are theorem-shaped refusals, siblings
  of `Effect4.Scope.key_freshness_refused` and
  `Effect4.Reason.host_memory_refused`; `FrameFiber.step_withFiber` and
  `FrameFiber.step_yieldableError` keep the behaviours. Census rows
  `op.WithFiber`, `op.YieldableError`, both `foreignBoundary`.
