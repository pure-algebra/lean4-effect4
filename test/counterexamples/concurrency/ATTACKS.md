# Concurrency representative attacks

These attacks belong to the bounded Fiber/scheduler/interruption and binary
`raceFirst` representatives. Stable IDs live in `../REGISTER.md`; executable
Lean witnesses live beside their owning representative under
`Effect4Test/Counterexamples/Concurrency/`.

## E4-CONC-CE-001 — untaped race

- **BROKE:** scheduler execution is deterministic without recording a choice.
- **WITNESS:** one initial state admits a worker-first step and a waiter-first
  step with different traces.
- **CLASS:** semantic nondeterminism.
- **FIXED-BY:** `SchedulerDecision.schedule`, `DecisionTape`, and a determinism
  theorem quantified over the same tape.

## E4-CONC-CE-002 — interrupt versus complete

- **BROKE:** interruption and completion commute, or their ordering may be
  omitted from replay evidence.
- **WITNESS:** interrupt-first records delivery; completion-first records
  completion. In each exact two-decision tape the second action refuses
  without changing that stopped machine, so the traces and replay results
  differ even when the terminal alphabet has only one value.
- **CLASS:** ordering ambiguity.
- **FIXED-BY:** both actions are first-order decisions, their order is retained
  by tape and trace, and `interrupt_complete_order_distinct` supplies the
  admitted production witness.

## E4-CONC-CE-003 — masked interruption

- **BROKE:** an interrupt request always becomes terminal interruption
  immediately.
- **WITNESS:** a masked fiber stays runnable with a pending request; unmasking
  changes it to finalizing interruption and clears the pending bit.
- **CLASS:** lifecycle collapse.
- **FIXED-BY:** explicit mask and pending-request state plus deferral and
  delivery-on-unmask laws; completion is admitted only after the mask is
  restored with no pending interruption.

## E4-CONC-CE-004 — lost finalizer

- **BROKE:** a terminal error projection contains enough information to prove
  cleanup safety.
- **WITNESS:** two machines project to the same interrupted terminal, while one
  ran cleanup and the other did not.
- **CLASS:** information erasure.
- **FIXED-BY:** machine state and observable trace outside the terminal arm,
  with cleanup count and lifecycle constrained by public laws.

## E4-CONC-CE-005 — double join

- **BROKE:** joining consumes the stored terminal result or may rerun cleanup.
- **WITNESS:** two observations return the same success and leave the cleanup
  count at one.
- **CLASS:** non-idempotent observation.
- **FIXED-BY:** join is read-only over stored terminal state; cleanup is a
  separate at-most-once transition.

## E4-CONC-CE-006 — empty operational relations

- **BROKE:** determinism and safety implications establish an adequate
  operational semantics by themselves.
- **WITNESS:** `EmptyStep := False` and `EmptyRuns := False` satisfy arbitrary
  one-step, two-step, and run postconditions whenever every law is guarded by
  a `Step` or `Runs` premise.
- **CLASS:** specification vacuity.
- **FIXED-BY:** `Machine.WellFormed`, admitted-total `Step`, exhaustive
  `stepEval` equations and trace deltas, total finite replay defined recursively
  through `Step`, fixed projections, inhabited positive clauses for every
  decision constructor, exact nil-tape classification, and one nonempty finite
  finished run.

## E4-CONC-CE-007 — duplicate cleanup history

- **BROKE:** a cleanup counter bounded by one proves observable at-most-once
  cleanup.
- **WITNESS:** a raw machine satisfies the pre-repair lifecycle and count
  admission but records the same cleanup identity twice.
- **CLASS:** trace/state incoherence.
- **FIXED-BY:** `Event.cleanupId?`, `Machine.cleanupEventIds`, the exact
  transition equation, and finite admission fields requiring cleanup event
  identities to be unique, closed over fibers, and equivalent to count one;
  `cleanup_events_at_most_once` exposes the run-level guarantee.

## E4-CONC-CE-008 — erased winner choice

- **BROKE:** scheduler state and scheduler decisions determine the binary race
  winner without an explicit race choice.
- **WITNESS:** one tied machine paired with the left winner and the same
  machine paired with the right winner has identical scheduler projection but
  distinct winner projection.
- **CLASS:** nondeterminism erasure.
- **FIXED-BY:** `RaceDecision.selectWinner`, `RaceState.winner`, and distinct
  fixed tapes for the two tie resolutions.

## E4-CONC-CE-009 — first completion collapsed into first success

- **BROKE:** first-completion and first-success racing are interchangeable.
- **WITNESS:** on the two-entry probe `[failed, succeeded]`, first completion
  observes the failed entry while first success observes the later successful
  entry.
- **CLASS:** semantic conflation.
- **FIXED-BY:** the representative is explicitly binary first completion over
  opaque `τ`; it contains no success predicate.  First-success semantics waits
  for the owning result classification.

## E4-CONC-CE-010 — early return before loser cleanup

- **BROKE:** the selected winner's terminal observation is enough to settle a
  race.
- **WITNESS:** the winner is done with a retained terminal value while the
  loser is finalizing, has cleanup count zero, and has no cleanup event.
- **CLASS:** resource-lifecycle truncation.
- **FIXED-BY:** `RaceState.Settled` requires both contenders done with cleanup
  done, and the settlement laws recover count-one and cleanup-event evidence.

## E4-CONC-CE-011 — masked loser misclassified

- **BROKE:** a selected masked loser with a pending interruption is settled or
  refused when the finite tape is depleted.
- **WITNESS:** the existing scheduler accepts `exitMask loser`, advances the
  loser to interruption finalization, and leaves cleanup pending.
- **CLASS:** frontier/refusal collapse.
- **FIXED-BY:** `RaceReplayResult.frontier`, post-selection loser-only unmask
  and cleanup decisions, and the masked-loser empty-tape frontier theorem.

## Claim limit

All eleven witnesses are finite. They do not prove a production implementation,
an exhaustive scheduler model, fairness, liveness, or Effect compatibility.


## Fork and supervision packet

CE-012 through CE-026 belong to
`test/contracts/fiber-supervision.contract.md`. Their Lean source is
`Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean`, namespace
`Effect4Test.Counterexamples.Concurrency.FiberSupervision`. All are finite
kernel-checked witnesses independent of the missing production module.
The preceding representative and binary-race attack meanings are unchanged.

### E4-CONC-CE-012 — post-start registration

- **BROKE:** Registering before immediate execution is observationally equivalent to registering afterward.
- **WITNESS:** `immediate_completion_not_tracked`. An already completed child is absent from the parent set; the same unpublished child is registered.
- **CLASS:** post-start registration.
- **FIXED-BY:** `forkUnsafe_immediate`, `commitFork_done_untracked`.

### E4-CONC-CE-013 — global versus local ownership

- **BROKE:** Installing the global middleware makes daemon fibers direct children.
- **WITNESS:** `daemon_parent_exit_distinction`. A live daemon is untracked even when middleware was installed earlier; only registered children enter parent waiting.
- **CLASS:** global versus local ownership.
- **FIXED-BY:** `forkChild_eq`, `forkDetach_eq`, `commitFork_daemon_untracked`, `beginParentExit_eq`.

### E4-CONC-CE-014 — incomplete observed world

- **BROKE:** An immediate child observation can reuse the pre-start parent and globals.
- **WITNESS:** `post_start_state_not_pre_state`. Startup may remove a sibling, allocate a nested fiber, and install middleware. Reusing pre-state resurrects or loses those observations.
- **CLASS:** incomplete observed world.
- **FIXED-BY:** `StartObservation.immediate` carries post-globals, post-parent, and post-child; `forkUnsafe_immediate` and `Globals.Extends` admit them explicitly.

### E4-CONC-CE-015 — publication before cleanup

- **BROKE:** A stored local body Exit is already available to join.
- **WITNESS:** `unpublished_body_exit`. A finalizing fiber holds Success 7 but has no published Exit; the done view exposes it.
- **CLASS:** publication before cleanup.
- **FIXED-BY:** `Fiber.published_iff`, `parentExitView_not_published_while_waiting`, `parentExitView_publication_requires_children`.

### E4-CONC-CE-016 — observation conflation

- **BROKE:** Await and join have the same failure observation.
- **WITNESS:** `await_failure_as_value`. Await succeeds with a failed Exit as its value; join resumes that same failed Exit as an effect.
- **CLASS:** observation conflation.
- **FIXED-BY:** `observation_await`, `observation_join`, `observation_value_ne_effect`.

### E4-CONC-CE-017 — call-order collapse

- **BROKE:** Interrupting and awaiting each child in sequence implements interruptAll.
- **WITNESS:** `request_all_before_wait`. An await inserted before the second request can block that request forever. Publications during a request remain allowed.
- **CLASS:** call-order collapse.
- **FIXED-BY:** `interruptAllRequests_eq`, `interruptAllWait_eq`, and actual-publication WaitState laws.

### E4-CONC-CE-018 — scope-policy conflation

- **BROKE:** forkIn and fiberRunIn share the same finalizer and closed-scope interruptor.
- **WITNESS:** `scope_binding_asymmetry`. forkIn skips self-interruption and uses the parent when already closed; fiberRunIn does not skip self and uses the child.
- **CLASS:** scope-policy conflation.
- **FIXED-BY:** `bindScope_closed`, `scopeFinalizerInterruptor_eq`, `scopeFinalizer_self_guard`.

### E4-CONC-CE-019 — observer-key drift

- **BROKE:** The child observer can remove a fresh or unrelated key.
- **WITNESS:** `shared_scope_key_required`. Removing key 37 leaves the linked finalizer at key 1; removing key 1 retains only the other slot.
- **CLASS:** observer-key drift.
- **FIXED-BY:** `bindScope_open`, `scopeObserver_eq`, `scopeObserver_key_membership`.

### E4-CONC-CE-020 — snapshot boundary loss

- **BROKE:** awaitAllChildren waits for every child ever seen.
- **WITNESS:** `only_new_children_awaited`. The current child set minus the initial snapshot excludes old siblings and does not resurrect finished children.
- **CLASS:** snapshot boundary loss.
- **FIXED-BY:** `newChildren_membership`, `awaitAllChildren_eq`.

### E4-CONC-CE-021 — cause erasure

- **BROKE:** A later interruption can overwrite the prior cause.
- **WITNESS:** `interruptors_accumulate`. Canonical Cause.combine retains two interruptor reasons where overwrite retains only the last.
- **CLASS:** cause erasure.
- **FIXED-BY:** `interruptCause_eq`, `Fiber.recordInterrupt_live`, `Fiber.recordInterrupt_done`.

### E4-CONC-CE-022 — failure observation loss

- **BROKE:** All-failure race reasons form a deduplicated set or use entrant order.
- **WITNESS:** `race_failure_order_and_duplicates`. Swapping callback arrival order changes the failure; duplicate reasons remain; all-empty causes still return Failure.
- **CLASS:** failure observation loss.
- **FIXED-BY:** `raceComplete_failure_last`, `raceComplete_failure_pending`, `race_two_failures`.

### E4-CONC-CE-023 — frontier collapse

- **BROKE:** An empty race or a selected winner with pending cleanup has finished.
- **WITNESS:** `race_empty_and_cleanup_frontiers`. Empty input stays pending; a winner waiting on a live masked child cannot return until actual publication.
- **CLASS:** frontier collapse.
- **FIXED-BY:** `race_empty_frontier`, `race_cleanup_result_requires_publications`, exact replay nil clauses.

### E4-CONC-CE-024 — reentrant branch timing

- **BROKE:** Every launched race loser is cleaned, or cleanup freezes a winner-time target snapshot.
- **WITNESS:** `race_reentrant_launch_branch`. A winner during entrant startup sees only already registered fibers. An empty set bypasses the late entrant; a nonempty branch reads the mutable set later and includes it.
- **CLASS:** reentrant branch timing.
- **FIXED-BY:** Split `beginLaunch`/`finishLaunch`, branch-only `cleanupNeeded`, `raceStep_beginCleanup`, `race_result_requires_start_finished`.
- **HOST WITNESS:** `harness/fiber-supervision/runtime-check.ts`, run against the exact pinned rc.112 runtime. This finite trace supplements the Lean countermodel and does not close host equivalence.

### E4-CONC-CE-025 — continuation profile overclaim

- **BROKE:** The local body Exit remains the eventual parent result under any later interruption.
- **WITNESS:** `parent_interruption_replaces_exit`. A body Success 7 survives a successful wait but a later parent interruption makes the wait fail and replaces it with Interrupt 99.
- **CLASS:** continuation profile overclaim.
- **FIXED-BY:** Restrict `beginParentExit`/`parentExitView` to the successful wait continuation with no intervening parent evaluation; keep the continuation bridge open.
- **HOST WITNESS:** `harness/fiber-supervision/runtime-check.ts`, run against the exact pinned rc.112 runtime. This finite trace supplements the Lean countermodel and does not close host equivalence.

### E4-CONC-CE-026 — dangling global identity

- **BROKE:** Post-parent allocation ownership alone admits the entire immediate observation.
- **WITNESS:** `post_start_child_ownership_required`. A valid post-parent can own no children while a valid new child owns ID 99 absent from post-globals; later fresh allocation can reuse it.
- **CLASS:** dangling global identity.
- **FIXED-BY:** `Globals.OwnsChildren postGlobals after`, `forkUnsafe_invalid_child_ownership`, and the matching positive `forkUnsafe_immediate` premise.

### Supervision claim limit

These 15 witnesses refute specific information losses or stronger claims.
They do not prove a production implementation, full continuation or scheduler
semantics, liveness, or host equivalence. In particular, Fiber.publish is a
terminal-view constructor given an externally justified actual publication;
none of these rows licenses arbitrary repeat publication as a runtime step.
The graph and clause ledger in `docs/SUPERVISION-DAG.md` retain the necessary
source interpretation and continuation obligations.
