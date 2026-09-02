import Lean
import Lean.Util.CollectAxioms
import Effect4.Concurrency.Scheduler

/-!
# Effect v4 fiber runtime coverage

This test-only checker joins the mechanical behaviour census of the pinned
`effect@4.0.0-rc.112` fiber runtime (`generated/effect-runtime-census.tsv`,
produced by `scripts/generate-effect-runtime-census.sh`) to the Lean
declarations that witness those behaviours.

The census keys are *observed runtime behaviours*, never "function X exists".
This module holds the frozen row list — one row per census id, carrying the
`PORT-MANIFEST.md` disposition, the declared coverage state, and the witness
declarations with their expected kernel dependency receipts. It fails the
build on a missing witness, a witness that is not a theorem, an axiom receipt
drift, a duplicate id, or an inconsistent disposition/coverage pairing.

Exact witness statements are frozen by the `#check (@name : proposition)`
ascriptions in the `StatementSnapshot` section below, which is the same
freezing idiom `Effect4Test/Concurrency/FiberRepresentativeContract.lean`
uses. `scripts/check-effect-runtime-census.sh` cross-checks that the snapshot
names and the emitted witness rows are the same list, in the same order, so
the ascriptions cannot be deleted without failing the gate.

Nothing here adds to or removes from the `Effect4` surface. The exact public
declaration census of `Effect4/Concurrency/*` is owned by
`Effect4Test/Concurrency/FiberAssurance.lean` and is untouched.
-/

open Lean Elab Command

namespace Effect4Test.Audit.RuntimeCoverage

universe u

section StatementSnapshot

open Effect4

/-! The exact proposition each witness proves, frozen by ascription. A drift in
any statement is a `type mismatch` at the offending line. -/

#check (@Effect4.masked_interrupt_defers :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before after : Machine τ}
    {requester target : FiberId} {requesterState targetState : FiberState τ},
    before.WellFormed →
      before.fiber requester = some requesterState →
        before.fiber target = some targetState →
          targetState.status.Active →
            targetState.mask = InterruptMask.masked →
              Step boundary before (SchedulerDecision.requestInterrupt requester target)
                  (StepResult.advanced after) →
                after.interruptPending target = some true ∧
                  after.terminal target = before.terminal target)

#check (@Effect4.unmask_delivers_pending :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before after : Machine τ}
    {target : FiberId} {current : FiberState τ},
    before.WellFormed →
      before.fiber target = some current →
        current.status.Active →
          current.mask = InterruptMask.masked →
            current.interruptPending = true →
              Step boundary before (SchedulerDecision.exitMask target) (StepResult.advanced after) →
                after.interruptPending target = some false ∧
                  after.mask target = some InterruptMask.unmasked ∧
                    after.terminal target = some boundary.interrupted ∧
                      Option.map FiberState.status (after.fiber target) = some FiberStatus.finalizing)

#check (@Effect4.pending_unmask_exists :
  ∀ {τ : Type u} (boundary : InterruptBoundary τ) {before : Machine τ} {target : FiberId}
    {current : FiberState τ},
    before.WellFormed →
      before.fiber target = some current →
        current.status.Active →
          current.mask = InterruptMask.masked →
            current.interruptPending = true →
              ∃ after,
                Step boundary before (SchedulerDecision.exitMask target) (StepResult.advanced after) ∧
                  after.terminal target = some boundary.interrupted ∧
                    Option.map FiberState.status (after.fiber target) = some FiberStatus.finalizing ∧
                      Event.interruptDelivered target ∈ after.trace)

#check (@Effect4.unmask_without_pending_exists :
  ∀ {τ : Type u} (boundary : InterruptBoundary τ) {before : Machine τ}
    {target : FiberId} {current : FiberState τ},
    before.WellFormed →
      before.fiber target = some current →
        current.status.Active →
          current.mask = InterruptMask.masked →
            current.interruptPending = false →
              ∃ after,
                Step boundary before (SchedulerDecision.exitMask target) (StepResult.advanced after) ∧
                  after.mask target = some InterruptMask.unmasked ∧
                    Event.maskExited target ∈ after.trace)

#check (@Effect4.enter_mask_exists :
  ∀ {τ : Type u} (boundary : InterruptBoundary τ) {before : Machine τ} {id : FiberId}
    {current : FiberState τ},
    before.WellFormed →
      before.fiber id = some current →
        current.status.Active →
          current.mask = InterruptMask.unmasked →
            ∃ after,
              Step boundary before (SchedulerDecision.enterMask id) (StepResult.advanced after) ∧
                after.mask id = some InterruptMask.masked ∧ Event.maskEntered id ∈ after.trace)

#check (@Effect4.unmasked_interrupt_delivers :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before after : Machine τ}
    {requester target : FiberId} {requesterState targetState : FiberState τ},
    before.WellFormed →
      before.fiber requester = some requesterState →
        before.fiber target = some targetState →
          targetState.status.Active →
            targetState.mask = InterruptMask.unmasked →
              Step boundary before (SchedulerDecision.requestInterrupt requester target)
                  (StepResult.advanced after) →
                after.terminal target = some boundary.interrupted ∧
                  Option.map FiberState.status (after.fiber target) = some FiberStatus.finalizing ∧
                    after.cleanupState target = some CleanupState.pending)

#check (@Effect4.unmasked_request_exists :
  ∀ {τ : Type u} (boundary : InterruptBoundary τ) {before : Machine τ}
    {requester target : FiberId} {requesterState targetState : FiberState τ},
    before.WellFormed →
      before.fiber requester = some requesterState →
        before.fiber target = some targetState →
          targetState.status.Active →
            targetState.mask = InterruptMask.unmasked →
              ∃ after,
                Step boundary before (SchedulerDecision.requestInterrupt requester target)
                    (StepResult.advanced after) ∧
                  after.terminal target = some boundary.interrupted ∧
                    Option.map FiberState.status (after.fiber target) = some FiberStatus.finalizing ∧
                      Event.interruptDelivered target ∈ after.trace)

#check (@Effect4.masked_request_exists :
  ∀ {τ : Type u} (boundary : InterruptBoundary τ) {before : Machine τ}
    {requester target : FiberId} {requesterState targetState : FiberState τ},
    before.WellFormed →
      before.fiber requester = some requesterState →
        before.fiber target = some targetState →
          targetState.status.Active →
            targetState.mask = InterruptMask.masked →
              ∃ after,
                Step boundary before (SchedulerDecision.requestInterrupt requester target)
                    (StepResult.advanced after) ∧
                  after.interruptPending target = some true ∧
                    Event.interruptDeferred target ∈ after.trace)

#check (@Effect4.join_agreement :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before after : Machine τ}
    {waiter target : FiberId} {targetState : FiberState τ} {result : τ},
    before.WellFormed →
      before.fiber target = some targetState →
        targetState.status = FiberStatus.done →
          Step boundary before (SchedulerDecision.join waiter target) (StepResult.advanced after) →
            before.terminal target = some result →
              after.terminal target = some result ∧
                after.cleanupState target = before.cleanupState target ∧
                  after.trace = before.trace ++ [Event.joinObserved waiter target result])

#check (@Effect4.double_join_agreement :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before middle after : Machine τ}
    {waiterOne waiterTwo target : FiberId} {targetState : FiberState τ} {result : τ},
    before.WellFormed →
      before.fiber target = some targetState →
        targetState.status = FiberStatus.done →
          waiterOne ≠ target →
            waiterTwo ≠ target →
              before.terminal target = some result →
                Step boundary before (SchedulerDecision.join waiterOne target)
                    (StepResult.advanced middle) →
                  Step boundary middle (SchedulerDecision.join waiterTwo target)
                      (StepResult.advanced after) →
                    middle.terminal target = some result ∧
                      after.terminal target = some result ∧
                        after.cleanupCount target = before.cleanupCount target)

#check (@Effect4.cleanup_preserves_terminal :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before after : Machine τ}
    {id : FiberId} {current : FiberState τ} {terminal : τ},
    before.WellFormed →
      before.fiber id = some current →
        current.status = FiberStatus.finalizing →
          current.terminal = some terminal →
            current.cleanup = CleanupState.pending →
              Step boundary before (SchedulerDecision.cleanup id) (StepResult.advanced after) →
                after.terminal id = some terminal ∧
                  Option.map FiberState.status (after.fiber id) = some FiberStatus.done ∧
                    after.cleanupState id = some CleanupState.done ∧
                      after.cleanupCount id = 1 ∧
                        after.trace = before.trace ++ [Event.cleanupFinished id])

#check (@Effect4.cleanup_at_most_once :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {initial : Machine τ} {tape : DecisionTape τ}
    {result : ReplayResult τ} {id : FiberId},
    initial.WellFormed → Runs boundary initial tape result → result.machine.cleanupCount id ≤ 1)

#check (@Effect4.cleanup_events_at_most_once :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {initial : Machine τ} {tape : DecisionTape τ}
    {result : ReplayResult τ},
    initial.WellFormed → Runs boundary initial tape result → result.machine.cleanupEventIds.Nodup)

#check (@Effect4.cleanup_count_monotone :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before : Machine τ}
    {decision : SchedulerDecision τ} {result : StepResult τ} {id : FiberId},
    before.WellFormed →
      Step boundary before decision result →
        before.cleanupCount id ≤ result.machine.cleanupCount id)

#check (@Effect4.cleanup_safe_on_finish :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {initial : Machine τ} {tape : DecisionTape τ}
    {final : Machine τ} {id : FiberId} {terminal : τ},
    initial.WellFormed →
      Runs boundary initial tape (ReplayResult.finished final) →
        final.terminal id = some terminal →
          final.cleanupState id = some CleanupState.done ∧ final.cleanupCount id = 1)

#check (@Effect4.step_deterministic :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {before : Machine τ}
    {decision : SchedulerDecision τ} {left right : StepResult τ},
    Step boundary before decision left → Step boundary before decision right → left = right)

#check (@Effect4.fixedTape_deterministic :
  ∀ {τ : Type u} {boundary : InterruptBoundary τ} {initial : Machine τ} {tape : DecisionTape τ}
    {left right : ReplayResult τ},
    Runs boundary initial tape left → Runs boundary initial tape right → left = right)

end StatementSnapshot

/-! ## The frozen census join -/

/-- One census row. `id` and `kind` must match `generated/effect-runtime-census.tsv`
exactly; the cross-check lives in `scripts/check-effect-runtime-census.sh`. -/
private structure Row where
  /-- Stable kebab id, identical to the census row id. -/
  id : String
  /-- Census kind, identical to the census row kind. -/
  kind : String
  /-- `PORT-MANIFEST.md` disposition vocabulary. -/
  disposition : String
  /-- `green`, `partial` or `absent`. -/
  coverage : String
  /-- Witness declarations with their expected canonical axiom receipt. -/
  witnesses : List (Name × String)

private def w (name : Name) (axioms : String) : Name × String := (name, axioms)

/-- Manifest dispositions that place a row outside the coverage denominator. -/
private def excludedDispositions : List String :=
  ["excludedInternal", "targetOnly", "evidenceOnly"]

private def knownDispositions : List String :=
  [ "owned", "split", "downstreamAdapter", "separateCalculus", "derivedExpansion"
  , "foreignBoundary", "targetOnly", "evidenceOnly", "excludedInternal" ]

private def knownKinds : List String :=
  [ "op", "frame-arm", "checkpoint", "interrupt", "fork", "scope", "scheduler"
  , "exit", "cause", "entry", "rule" ]

private def knownCoverage : List String := ["green", "partial", "absent"]

private def censusRows : List Row :=
  [ { id := "op.Success", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.Failure", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.WithFiber", kind := "op", disposition := "foreignBoundary", coverage := "absent", witnesses := [] }
  , { id := "op.YieldableError", kind := "op", disposition := "foreignBoundary", coverage := "absent", witnesses := [] }
  , { id := "op.Sync", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.Suspend", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.Yield", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.Async", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.AsyncFinalizer", kind := "op", disposition := "excludedInternal", coverage := "absent", witnesses := [] }
  , { id := "op.Iterator", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.OnSuccess", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.OnFailure", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.OnSuccessAndFailure", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.Exit", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.OnExit", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.SetInterruptible", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.While", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.OnSuccess", kind := "frame-arm", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.OnFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.OnSuccessAndFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.Exit", kind := "frame-arm", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.OnExit", kind := "frame-arm", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.cleanup_preserves_terminal "propext"
        , w `Effect4.cleanup_at_most_once "propext,Quot.sound"
        , w `Effect4.cleanup_events_at_most_once "propext,Quot.sound"
        , w `Effect4.cleanup_count_monotone "propext,Quot.sound"
        , w `Effect4.cleanup_safe_on_finish "propext,Quot.sound" ] }
  , { id := "frame-arm.SetInterruptible", kind := "frame-arm", disposition := "owned", coverage := "partial"
    , witnesses := [ w `Effect4.enter_mask_exists "propext" ] }
  , { id := "frame-arm.AsyncFinalizer", kind := "frame-arm", disposition := "excludedInternal", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.While", kind := "frame-arm", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.Iterator", kind := "frame-arm", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.runloop-top", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.getcont-deferred", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.post-yield-cancel", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.exit-failcause-skip", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.set-fiber-interruptible", kind := "checkpoint", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.pending_unmask_exists "propext"
        , w `Effect4.unmask_without_pending_exists "propext" ] }
  , { id := "checkpoint.set-interruptible-contall", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "interrupt.unsafe-entry", kind := "interrupt", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.unmasked_interrupt_delivers "propext"
        , w `Effect4.unmasked_request_exists "propext"
        , w `Effect4.masked_request_exists "propext" ] }
  , { id := "interrupt.accumulate", kind := "interrupt", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.unsafe", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.child", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.detach", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.in", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.scoped", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.race-all", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.await-all-children", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.fiber-run-in", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.join", kind := "fork", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.join_agreement "propext"
        , w `Effect4.double_join_agreement "propext" ] }
  , { id := "fork.await", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.interrupt", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "fork.interrupt-all", kind := "fork", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.states", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.make", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.add-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.add-after-closed", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.remove-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.close-state-first", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.close-lifo", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.close-sequential", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.close-parallel", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.close-merge", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.exit-as-void-all", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.fork-linkage", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.scoped", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scope.acquire-release", kind := "scope", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "scheduler.should-yield", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.priority-buckets", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.dispatcher-arming", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.run-tasks-drain-once", kind := "scheduler", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.step_deterministic "none"
        , w `Effect4.fixedTape_deterministic "propext,Quot.sound" ] }
  , { id := "scheduler.flush", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.yield-now-resume-guard", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.max-ops-default", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.prevent-yield-default", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "scheduler.host-loop", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "exit.success-failure", kind := "exit", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "exit.reason-alphabet", kind := "exit", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.flat-reasons", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.reason-fail", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.reason-die", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.reason-interrupt", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.combine-union", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.finalizer-merge", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.squash", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.union-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.dedupe-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "cause.annotations", kind := "cause", disposition := "foreignBoundary", coverage := "absent", witnesses := [] }
  , { id := "entry.run-fork-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.abort-signal", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-callback-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-promise-exit-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-promise-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-sync-exit-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.async-fiber-error", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.with-error-reporting", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "rule.frames-are-primitives", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.interrupt-bypasses-handlers", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.yield-is-overloaded", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.only-fork-child-tracks", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.children-interrupted-after-exit", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.scope-close-lifo-state-first", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.cause-has-no-structure", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "rule.start-is-asymmetric", kind := "rule", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "rule.record-and-apply-separate", kind := "rule", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.masked_interrupt_defers "propext"
        , w `Effect4.unmask_delivers_pending "propext" ] }
  , { id := "rule.budget-per-runloop-entry", kind := "rule", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  ]

/-- The witness names frozen by `StatementSnapshot`, in snapshot order.
`scripts/check-effect-runtime-census.sh` compares this list, as emitted, with
the `#check (@…` occurrences in this file, so a deleted ascription fails. -/
private def snapshotWitnesses : List Name :=
  [ `Effect4.masked_interrupt_defers
  , `Effect4.unmask_delivers_pending
  , `Effect4.pending_unmask_exists
  , `Effect4.unmask_without_pending_exists
  , `Effect4.enter_mask_exists
  , `Effect4.unmasked_interrupt_delivers
  , `Effect4.unmasked_request_exists
  , `Effect4.masked_request_exists
  , `Effect4.join_agreement
  , `Effect4.double_join_agreement
  , `Effect4.cleanup_preserves_terminal
  , `Effect4.cleanup_at_most_once
  , `Effect4.cleanup_events_at_most_once
  , `Effect4.cleanup_count_monotone
  , `Effect4.cleanup_safe_on_finish
  , `Effect4.step_deterministic
  , `Effect4.fixedTape_deterministic
  ]

private def expectedRowTotal : Nat := 99
private def expectedDenominator : Nat := 79

/-! ## Checks -/

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"runtime coverage mismatch: {detail}"

private def firstDuplicateString? : List String → Option String
  | [] => none
  | value :: values => if values.contains value then some value else firstDuplicateString? values

private def firstDuplicateName? : List Name → Option Name
  | [] => none
  | name :: names => if names.contains name then some name else firstDuplicateName? names

/-- Canonical kernel dependency text for one witness. A witness is a semantic
theorem, so it is bound by the semantic ceiling `propext`/`Quot.sound`; any
other axiom, `Classical.choice` included, fails here rather than being spelled
into a receipt. -/
private def canonicalAxiomText (name : Name) : CommandElabM String := do
  let actual := (← collectAxioms name).toList
  let unknown := actual.filter fun axiomName =>
    axiomName != ``propext && axiomName != ``Quot.sound
  unless unknown.isEmpty do
    failJoin m!"unexpected kernel axioms for witness {name}: {unknown}"
  let parts := [``propext, ``Quot.sound].filter actual.contains
  pure <| if parts.isEmpty then "none" else
    String.intercalate "," (parts.map fun n => n.toString)

private def checkRowShape : CommandElabM Unit := do
  if let some duplicate := firstDuplicateString? (censusRows.map Row.id) then
    failJoin m!"duplicate census row id: {duplicate}"
  unless censusRows.length == expectedRowTotal do
    failJoin m!"census row count drifted: {censusRows.length}, expected {expectedRowTotal}"
  for row in censusRows do
    unless knownKinds.contains row.kind do
      failJoin m!"row {row.id} has unknown kind {row.kind}"
    unless knownDispositions.contains row.disposition do
      failJoin m!"row {row.id} has a disposition outside the PORT-MANIFEST vocabulary: {row.disposition}"
    unless knownCoverage.contains row.coverage do
      failJoin m!"row {row.id} has unknown coverage {row.coverage}"
    if let some duplicate := firstDuplicateName? (row.witnesses.map Prod.fst) then
      failJoin m!"row {row.id} lists witness {duplicate} twice"
    let hasWitness := !row.witnesses.isEmpty
    if row.coverage == "absent" && hasWitness then
      failJoin m!"row {row.id} is declared absent but carries witnesses"
    if row.coverage != "absent" && !hasWitness then
      failJoin m!"row {row.id} is declared {row.coverage} but carries no witness"
    if row.disposition == "owned" && !hasWitness then
      failJoin m!"row {row.id} is owned and must carry at least one witness"
    if excludedDispositions.contains row.disposition && hasWitness then
      failJoin m!"row {row.id} is {row.disposition}, is outside the coverage denominator, and must carry no witness"

private def checkWitnesses : CommandElabM Unit := do
  let environment ← getEnv
  for row in censusRows do
    for (name, expectedAxioms) in row.witnesses do
      match environment.find? name with
      | none => failJoin m!"row {row.id}: missing witness declaration {name}"
      | some (.thmInfo _) => pure ()
      | some info =>
          let statementIsProp ← liftTermElabM <| Meta.isProp info.type
          let kind :=
            if statementIsProp then "a Prop-typed non-theorem declaration" else "not a theorem"
          failJoin m!"row {row.id}: witness {name} is {kind}; a witness must be a theorem"
      let actualAxioms ← canonicalAxiomText name
      unless actualAxioms == expectedAxioms do
        failJoin
          m!"row {row.id}: axiom receipt for {name}: expected {expectedAxioms}, found {actualAxioms}"

private def checkSnapshot : CommandElabM Unit := do
  if let some duplicate := firstDuplicateName? snapshotWitnesses then
    failJoin m!"statement snapshot lists {duplicate} twice"
  let used := censusRows.flatMap fun row => row.witnesses.map Prod.fst
  let missing := used.filter fun name => !snapshotWitnesses.contains name
  unless missing.isEmpty do
    failJoin m!"witnesses without a frozen statement snapshot: {missing}"
  let stale := snapshotWitnesses.filter fun name => !used.contains name
  unless stale.isEmpty do
    failJoin m!"statement snapshot entries that witness no census row: {stale}"

private def denominatorRows : List Row :=
  censusRows.filter fun row => !excludedDispositions.contains row.disposition

private def checkCoverageArithmetic : CommandElabM Unit := do
  unless denominatorRows.length == expectedDenominator do
    failJoin
      m!"coverage denominator drifted: {denominatorRows.length}, expected {expectedDenominator}"

private def checkRuntimeCoverage : CommandElabM Unit := do
  checkRowShape
  checkWitnesses
  checkSnapshot
  checkCoverageArithmetic
  let total := censusRows.length
  let denominator := denominatorRows.length
  let excluded := total - denominator
  let green := (denominatorRows.filter fun row => row.coverage == "green").length
  let partial_ := (denominatorRows.filter fun row => row.coverage == "partial").length
  let absent := (denominatorRows.filter fun row => row.coverage == "absent").length
  let ownedGreen :=
    (denominatorRows.filter fun row => row.disposition == "owned" && row.coverage == "green").length
  let partialIds := (denominatorRows.filter fun row => row.coverage == "partial").map Row.id
  let absentIds := (denominatorRows.filter fun row => row.coverage == "absent").map Row.id
  logInfo m!"Effect v4 runtime coverage: {total} census rows; {excluded} excluded by disposition; denominator {denominator}; owned-with-green {ownedGreen}/{denominator}; green {green}, partial {partial_}, absent {absent}"
  logInfo m!"partial rows: {partialIds}"
  logInfo m!"absent rows: {absentIds}"

private def emitRuntimeCoverage : CommandElabM Unit := do
  checkRuntimeCoverage
  for row in censusRows do
    liftIO <| IO.println
      s!"E4RTCOV\trow\t{row.id}\t{row.kind}\t{row.disposition}\t{row.coverage}\t{row.witnesses.length}"
  for row in censusRows do
    for (name, _) in row.witnesses do
      let actual ← canonicalAxiomText name
      liftIO <| IO.println s!"E4RTCOV\twitness\t{row.id}\t{name}\t{actual}"
  for name in snapshotWitnesses do
    liftIO <| IO.println s!"E4RTCOV\tsnapshot\t{name}"
  let denominator := denominatorRows.length
  let green := (denominatorRows.filter fun row => row.coverage == "green").length
  let partial_ := (denominatorRows.filter fun row => row.coverage == "partial").length
  let absent := (denominatorRows.filter fun row => row.coverage == "absent").length
  let ownedGreen :=
    (denominatorRows.filter fun row => row.disposition == "owned" && row.coverage == "green").length
  liftIO <| IO.println
    s!"E4RTCOV\tcoverage\t{censusRows.length}\t{denominator}\t{ownedGreen}\t{green}\t{partial_}\t{absent}"

syntax (name := effect4CheckRuntimeCoverage)
  "#effect4_check_runtime_coverage" : command

syntax (name := effect4EmitRuntimeCoverage)
  "#effect4_emit_runtime_coverage" : command

elab_rules : command
  | `(#effect4_check_runtime_coverage) => checkRuntimeCoverage

elab_rules : command
  | `(#effect4_emit_runtime_coverage) => emitRuntimeCoverage

#effect4_check_runtime_coverage
#effect4_emit_runtime_coverage

end Effect4Test.Audit.RuntimeCoverage
