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
