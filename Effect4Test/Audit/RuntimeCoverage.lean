import Lean
import Lean.Util.CollectAxioms
import Effect4.Concurrency.Scheduler
import Effect4.Concurrency.Supervision
import Effect4.Semantics.Cause
import Effect4.Semantics.Exit
import Effect4.Runtime.Scope
import Effect4.Runtime.Runtime

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

universe u v

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

/-! The Cause/Exit model witnesses. Statements are transcribed from the frozen
ascriptions of `Effect4Test/Semantics/CauseExitContract.lean`. -/

#check (@Effect4.Cause.eq_iff : forall {ε δ ι α : Type u} (left right : Cause ε δ ι α),
  left = right <-> left.reasons = right.reasons)

#check (@Effect4.Cause.ext : forall {ε δ ι α : Type u} {left right : Cause ε δ ι α},
  left.reasons = right.reasons -> left = right)

#check (@Effect4.Cause.eq_iff_pointwise :
  forall {ε δ ι α : Type u} (left right : Cause ε δ ι α),
    left = right <->
      (left.reasons.length = right.reasons.length /\
        forall index : Nat, left.reasons[index]? = right.reasons[index]?))

#check (@Effect4.Cause.combine_no_new_reason : forall {ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (self that : Cause ε δ ι α),
  reason ∈ (Cause.combine self that).reasons ->
    reason ∈ self.reasons \/ reason ∈ that.reasons)

#check (@Effect4.Reason.error_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).error? = some error)

#check (@Effect4.Reason.annotations_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).annotations = annotations)

#check (@Effect4.Reason.fail_inj : forall {ε δ ι α : Type u} (leftError rightError : ε)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.fail leftError leftAnnotations : Reason ε δ ι α) =
      Reason.fail rightError rightAnnotations <->
    leftError = rightError /\ leftAnnotations = rightAnnotations)

#check (@Effect4.Reason.defect_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).defect? = some defect)

#check (@Effect4.Reason.annotations_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).annotations = annotations)

#check (@Effect4.Reason.die_inj : forall {ε δ ι α : Type u} (leftDefect rightDefect : δ)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.die leftDefect leftAnnotations : Reason ε δ ι α) =
      Reason.die rightDefect rightAnnotations <->
    leftDefect = rightDefect /\ leftAnnotations = rightAnnotations)

#check (@Effect4.Cause.interrupt_reasons : forall {ε δ ι α : Type u}
  (interruptor : Option ι),
  (Cause.interrupt interruptor : Cause ε δ ι α).reasons =
    [Reason.interrupt interruptor ReasonAnnotations.empty])

#check (@Effect4.Reason.annotations_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι) (annotations : ReasonAnnotations α),
  (Reason.interrupt interruptor annotations : Reason ε δ ι α).annotations =
    annotations)

#check (@Effect4.Reason.interrupt_inj : forall {ε δ ι α : Type u}
  (leftInterruptor rightInterruptor : Option ι)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.interrupt leftInterruptor leftAnnotations : Reason ε δ ι α) =
      Reason.interrupt rightInterruptor rightAnnotations <->
    leftInterruptor = rightInterruptor /\
      leftAnnotations = rightAnnotations)

#check (@Effect4.Cause.combine_empty_left : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (that : Cause ε δ ι α),
  Cause.combine Cause.empty that = that)

#check (@Effect4.Cause.combine_empty_right : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α),
  Cause.combine self Cause.empty = self)

#check (@Effect4.Cause.combine_reasons : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons ≠ [] -> that.reasons ≠ [] ->
  (Cause.combine self that).reasons =
    Cause.dedup (self.reasons ++ that.reasons))

#check (@Effect4.Cause.mem_combine : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (self that : Cause ε δ ι α),
  reason ∈ (Cause.combine self that).reasons <->
    reason ∈ self.reasons \/ reason ∈ that.reasons)

#check (@Effect4.Cause.combine_self : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α),
  self.reasons.Nodup -> Cause.combine self self = self)

#check (@Effect4.Cause.combine_order : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons.Nodup -> that.reasons.Nodup ->
  (Cause.combine self that).reasons =
    self.reasons ++
      that.reasons.filter (fun reason => decide (reason ∉ self.reasons)))

#check (@Effect4.Cause.dedup_cons : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (rest : List (Reason ε δ ι α)),
  Cause.dedup (reason :: rest) =
    reason :: (Cause.dedup rest).filter (fun other => decide (other ≠ reason)))

#check (@Effect4.Cause.mem_dedup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (list : List (Reason ε δ ι α)),
  reason ∈ Cause.dedup list <-> reason ∈ list)

#check (@Effect4.Cause.dedup_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (list : List (Reason ε δ ι α)), (Cause.dedup list).Nodup)

#check (@Effect4.Cause.dedup_of_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (list : List (Reason ε δ ι α)), list.Nodup -> Cause.dedup list = list)

#check (@Effect4.Exit.mergeFinalizer_failure_failure : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (cause finalizerCause : Cause ε δ ι α),
  Exit.mergeFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause))

#check (@Effect4.Exit.restoreAfterFinalizer_failure_failure :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (cause finalizerCause : Cause ε δ ι α),
  Exit.restoreAfterFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause))

#check (@Effect4.Exit.mergeFinalizer_success_failure : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (value : β) (finalizerCause : Cause ε δ ι α),
  Exit.mergeFinalizer (Exit.success value) (Exit.failure finalizerCause) =
    Exit.failure finalizerCause)

#check (@Effect4.Exit.restoreAfterFinalizer_success_failure :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (value : β) (finalizerCause : Cause ε δ ι α),
  Exit.restoreAfterFinalizer (Exit.success value : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure finalizerCause)

#check (@Effect4.Cause.squash_error : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (error : ε) (rest : List ε),
  self.reasons.filterMap Reason.error? = error :: rest ->
    self.squash = Squashed.error error)

#check (@Effect4.Cause.squash_defect : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (defect : δ) (rest : List δ),
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = defect :: rest ->
    self.squash = Squashed.defect defect)

#check (@Effect4.Cause.squash_interrupted : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α),
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = [] ->
  self.reasons ≠ [] ->
    self.squash = Squashed.interruptedWithoutError)

#check (@Effect4.Cause.squash_emptyCause_iff : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α),
  self.squash = Squashed.emptyCause <-> self.reasons = [])

#check (@Effect4.Cause.squash_fail_over_die : forall {ε δ ι α : Type u} (error : ε)
  (defect : δ) (dieAnnotations failAnnotations : ReasonAnnotations α),
  (Cause.mk [Reason.die defect dieAnnotations,
      Reason.fail error failAnnotations] : Cause ε δ ι α).squash =
    Squashed.error error)

#check (@Effect4.ReasonAnnotations.keys_nodup : forall {α : Type u} (self : ReasonAnnotations α),
  self.keys.Nodup)

#check (@Effect4.Reason.annotate_annotations : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α) (extra : ReasonAnnotations α) (overwrite : Bool),
  (reason.annotate extra overwrite).annotations =
    reason.annotations.annotate extra overwrite)

#check (@Effect4.Reason.host_memory_refused :
  forall {ε α : Type u} (recall : ε -> ReasonAnnotations α) (left right : ε),
    left = right -> recall left = recall right)

#check (@Effect4.ReasonAnnotations.annotate_entries :
  forall {α : Type u} (self extra : ReasonAnnotations α) (overwrite : Bool),
    (self.annotate extra overwrite).entries =
      self.entries.map (fun entry =>
        if overwrite = true then
          match extra.lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) ++
      extra.entries.filter (fun entry => decide (entry.fst ∉ self.keys)))

#check (@Effect4.ReasonAnnotations.lookup_annotate_kept :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α),
    self.lookup key = some value ->
    (self.annotate extra false).lookup key = some value)

#check (@Effect4.ReasonAnnotations.lookup_annotate_overwrite :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α),
    extra.lookup key = some value ->
    (self.annotate extra true).lookup key = some value)

#check (@Effect4.Exit.cases_receipt : forall {β ε δ ι α : Type u}
  (self : Exit β ε δ ι α),
  (exists value, self = Exit.success value) \/
  (exists cause, self = Exit.failure cause))

#check (@Effect4.Exit.success_ne_failure : forall {β ε δ ι α : Type u} (value : β)
  (cause : Cause ε δ ι α),
  (Exit.success value : Exit β ε δ ι α) ≠ Exit.failure cause)

#check (@Effect4.Exit.success_inj : forall {β ε δ ι α : Type u} (left right : β),
  (Exit.success left : Exit β ε δ ι α) = Exit.success right <-> left = right)

#check (@Effect4.Exit.failure_inj : forall {β ε δ ι α : Type u}
  (left right : Cause ε δ ι α),
  (Exit.failure left : Exit β ε δ ι α) = Exit.failure right <-> left = right)

#check (@Effect4.Exit.cause_failure : forall {β ε δ ι α : Type u}
  (cause : Cause ε δ ι α),
  (Exit.failure cause : Exit β ε δ ι α).cause? = some cause)

#check (@Effect4.ReasonTag.all_nodup : ReasonTag.all.Nodup)

#check (@Effect4.ReasonTag.mem_all : forall tag : ReasonTag, tag ∈ ReasonTag.all)

#check (@Effect4.ReasonTag.cases_receipt : forall tag : ReasonTag,
  tag = ReasonTag.fail \/ tag = ReasonTag.die \/ tag = ReasonTag.interrupt)

#check (@Effect4.Reason.cases_receipt : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α),
  (exists error annotations, reason = Reason.fail error annotations) \/
  (exists defect annotations, reason = Reason.die defect annotations) \/
  (exists interruptor annotations,
    reason = Reason.interrupt interruptor annotations))

#check (@Effect4.Reason.tag_mem_all : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α), reason.tag ∈ ReasonTag.all)

#check (@Effect4.Exit.asVoidAll_reasons : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)),
  (Exit.asVoidAll exits).causeReasons = exits.flatMap Exit.causeReasons)

#check (@Effect4.Exit.asVoidAll_failure : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)) (reason : Reason ε δ ι α)
  (rest : List (Reason ε δ ι α)),
  exits.flatMap Exit.causeReasons = reason :: rest ->
    Exit.asVoidAll exits = Exit.failure (Cause.mk (reason :: rest)))

#check (@Effect4.Exit.asVoidAll_all_success : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)),
  (forall exit, exit ∈ exits -> exists value, exit = Exit.success value) ->
    Exit.asVoidAll exits = Exit.success ())

#check (@Effect4.Exit.void_eq : forall {ε δ ι α : Type u},
  (Exit.void : Exit Unit ε δ ι α) = Exit.success ())

/-! The Scope model witnesses. Statements are transcribed from the frozen
ascriptions of `Effect4Test/Runtime/ScopeContract.lean`. -/

#check (@Effect4.ScopeState.cases_receipt :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state = Effect4.ScopeState.empty \/
      state = Effect4.ScopeState.openEmpty \/
        (exists key finalizer, state = Effect4.ScopeState.openInline key finalizer) \/
          (exists table, state = Effect4.ScopeState.openMap table) \/
            (exists exit, state = Effect4.ScopeState.closed exit))

#check (@Effect4.ScopeState.entries_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.empty : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

#check (@Effect4.ScopeState.entries_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

#check (@Effect4.ScopeState.entries_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (key : κ) (finalizer : φ),
    (Effect4.ScopeState.openInline key finalizer :
      Effect4.ScopeState κ φ β ε δ ι α).entries = [(key, finalizer)])

#check (@Effect4.ScopeState.entries_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (table : List (κ × φ)),
    (Effect4.ScopeState.openMap table : Effect4.ScopeState κ φ β ε δ ι α).entries = table)

#check (@Effect4.ScopeState.entries_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

#check (@Effect4.ScopeState.isOpen_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.empty : Effect4.ScopeState κ φ β ε δ ι α).isOpen = false)

#check (@Effect4.ScopeState.isOpen_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)

#check (@Effect4.ScopeState.isOpen_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (key : κ) (finalizer : φ),
    (Effect4.ScopeState.openInline key finalizer :
      Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)

#check (@Effect4.ScopeState.isOpen_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (table : List (κ × φ)),
    (Effect4.ScopeState.openMap table : Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)

#check (@Effect4.ScopeState.isOpen_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).isOpen = false)

#check (@Effect4.ScopeState.isClosed_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state.isClosed = true <-> exists exit, state = Effect4.ScopeState.closed exit)

#check (@Effect4.ScopeState.closingExit_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).closingExit? =
      some exit)

#check (@Effect4.ScopeState.closingExit_of_not_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state.isClosed = false -> state.closingExit? = none)

#check (@Effect4.ScopeState.openEmpty_ne_openMap_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α) ≠
      Effect4.ScopeState.openMap [])

#check (@Effect4.Scope.finalizers_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizers = self.state.entries)

#check (@Effect4.Scope.finalizerKeys_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizerKeys = self.finalizers.map Prod.fst)

#check (@Effect4.Scope.finalizerCount_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizerCount = self.finalizers.length)

#check (@Effect4.Scope.finalizerCount_not_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.isOpen = false -> self.finalizerCount = 0)

#check (@Effect4.FinalizerStrategy.all_nodup : Effect4.FinalizerStrategy.all.Nodup)

#check (@Effect4.FinalizerStrategy.mem_all :
  forall strategy : Effect4.FinalizerStrategy, strategy ∈ Effect4.FinalizerStrategy.all)

#check (@Effect4.Scope.make_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).strategy = strategy)

#check (@Effect4.Scope.make_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).state =
      Effect4.ScopeState.empty)

#check (@Effect4.Scope.make_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).finalizers = [])

#check (@Effect4.Scope.makeDefault_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.makeDefault : Effect4.Scope κ φ β ε δ ι α) =
      Effect4.Scope.make Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.makeDefault_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.makeDefault : Effect4.Scope κ φ β ε δ ι α).strategy =
      Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.key_freshness_refused :
  forall {κ : Type u} {γ : Type u} (mint : γ -> κ) (left right : γ),
    left = right -> mint left = mint right)

#check (@Effect4.Scope.tableInsert_new : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∉ table.map Prod.fst ->
    Effect4.Scope.tableInsert table key finalizer = table ++ [(key, finalizer)])

#check (@Effect4.Scope.tableInsert_existing : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∈ table.map Prod.fst ->
    Effect4.Scope.tableInsert table key finalizer =
      table.map (fun entry => if entry.fst = key then (key, finalizer) else entry))

#check (@Effect4.Scope.tableInsert_keys_of_mem : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∈ table.map Prod.fst ->
    (Effect4.Scope.tableInsert table key finalizer).map Prod.fst = table.map Prod.fst)

#check (@Effect4.Scope.tableInsert_nodup : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  (table.map Prod.fst).Nodup ->
    ((Effect4.Scope.tableInsert table key finalizer).map Prod.fst).Nodup)

#check (@Effect4.Scope.addUnsafe_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    (self.addUnsafe key finalizer).strategy = self.strategy)

#check (@Effect4.Scope.addUnsafe_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.empty ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openInline key finalizer)

#check (@Effect4.Scope.addUnsafe_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openEmpty ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openInline key finalizer)

#check (@Effect4.Scope.addUnsafe_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (existing finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey existing ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openMap
          (Effect4.Scope.tableInsert [(existingKey, existing)] key finalizer))

#check (@Effect4.Scope.addUnsafe_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openMap table ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openMap (Effect4.Scope.tableInsert table key finalizer))

#check (@Effect4.Scope.addUnsafe_promotes :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (existing finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey existing -> existingKey ≠ key ->
      (self.addUnsafe key finalizer).finalizers =
        [(existingKey, existing), (key, finalizer)])

#check (@Effect4.Scope.addUnsafe_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = false -> key ∉ self.finalizerKeys ->
      (self.addUnsafe key finalizer).finalizers = self.finalizers ++ [(key, finalizer)])

#check (@Effect4.Scope.addUnsafe_keys_nodup :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.finalizerKeys.Nodup -> (self.addUnsafe key finalizer).finalizerKeys.Nodup)

#check (@Effect4.Scope.addUnsafe_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = true -> self.addUnsafe key finalizer = self)

#check (@Effect4.Scope.addExit_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = false ->
      Effect4.Scope.addExit run self key finalizer =
        (self.addUnsafe key finalizer, Effect4.Exit.void))

#check (@Effect4.Scope.addExit_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ)
    (exit : Effect4.Exit β ε δ ι α),
    self.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.addExit run self key finalizer = (self, run finalizer exit))

#check (@Effect4.Scope.addExit_closed_registers_nothing :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ)
    (exit : Effect4.Exit β ε δ ι α),
    self.state = Effect4.ScopeState.closed exit ->
      (Effect4.Scope.addExit run self key finalizer).fst.finalizers = [])

#check (@Effect4.Scope.tableRemove_eq : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  Effect4.Scope.tableRemove table key =
    table.filter (fun entry => decide (entry.fst ≠ key)))

#check (@Effect4.Scope.tableRemove_keys : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  key ∉ (Effect4.Scope.tableRemove table key).map Prod.fst)

#check (@Effect4.Scope.tableRemove_nodup : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  (table.map Prod.fst).Nodup ->
    ((Effect4.Scope.tableRemove table key).map Prod.fst).Nodup)

#check (@Effect4.Scope.removeUnsafe_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    (self.removeUnsafe key).strategy = self.strategy)

#check (@Effect4.Scope.removeUnsafe_inline_hit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openInline key finalizer ->
      (self.removeUnsafe key).state = Effect4.ScopeState.openEmpty)

#check (@Effect4.Scope.removeUnsafe_inline_miss :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey finalizer -> existingKey ≠ key ->
      self.removeUnsafe key = self)

#check (@Effect4.Scope.removeUnsafe_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ),
    self.state = Effect4.ScopeState.openMap table ->
      (self.removeUnsafe key).state =
        Effect4.ScopeState.openMap (Effect4.Scope.tableRemove table key))

#check (@Effect4.Scope.removeUnsafe_not_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    self.isOpen = false -> self.removeUnsafe key = self)

#check (@Effect4.Scope.removeUnsafe_keys :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    key ∉ (self.removeUnsafe key).finalizerKeys)

#check (@Effect4.Scope.removeUnsafe_keys_nodup :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    self.finalizerKeys.Nodup -> (self.removeUnsafe key).finalizerKeys.Nodup)

#check (@Effect4.Scope.close_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.close run self exit =
      (Effect4.Scope.closeState self exit, Effect4.Scope.closeResult run self exit))

#check (@Effect4.Scope.close_state_independent_of_run :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (leftRun rightRun : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.close leftRun self exit).fst =
      (Effect4.Scope.close rightRun self exit).fst)

#check (@Effect4.Scope.closeState_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeState self exit).state = Effect4.ScopeState.closed exit)

#check (@Effect4.Scope.closeState_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).strategy = self.strategy)

#check (@Effect4.Scope.closeState_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).finalizers = [])

#check (@Effect4.Scope.closeState_isClosed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).isClosed = true)

#check (@Effect4.Scope.closeState_idempotent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.closeState self exit = self)

#check (@Effect4.Scope.close_closingExit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeState self exit).closingExit? = some exit)

#check (@Effect4.Scope.close_idempotent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.close run self exit = (self, Effect4.Exit.void))

#check (@Effect4.Scope.close_twice :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (first second : Effect4.Exit β ε δ ι α),
    Effect4.Scope.close run (Effect4.Scope.close run self first).fst second =
      ((Effect4.Scope.close run self first).fst, Effect4.Exit.void))

#check (@Effect4.Scope.close_reentrant_add :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (key : κ)
    (finalizer : φ),
    self.isClosed = false ->
      Effect4.Scope.addExit run (Effect4.Scope.closeState self exit) key finalizer =
        (Effect4.Scope.closeState self exit, run finalizer exit))

#check (@Effect4.Scope.closeResult_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.closeResult run self exit = Effect4.Exit.void)

#check (@Effect4.Scope.closeOrder_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.closeOrder = (self.finalizers.map Prod.snd).reverse)

#check (@Effect4.Scope.closeOrder_last_first :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (table : List (κ × φ)) (key : κ) (finalizer : φ),
    self.finalizers = table ++ [(key, finalizer)] ->
      self.closeOrder = finalizer :: (table.map Prod.snd).reverse)

#check (@Effect4.Scope.closeExits_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.closeExits run self exit =
      self.closeOrder.map (fun finalizer => run finalizer exit))

#check (@Effect4.Scope.closeExits_reverse :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.closeExits run self exit =
      self.finalizers.reverse.map (fun entry => run entry.snd exit))

#check (@Effect4.Scope.runScoped_lifo :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (registrations.map Prod.fst).Nodup ->
      Effect4.Scope.closeExits run
          ((Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
            Effect4.Scope κ φ β ε δ ι α).addAll registrations) bodyExit =
        registrations.reverse.map (fun entry => run entry.snd bodyExit))

#check (@Effect4.Scope.closeExits_length :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeExits run self exit).length = self.finalizers.length)

#check (@Effect4.Scope.closeResult_reasons :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeResult run self exit).causeReasons =
        (Effect4.Scope.closeExits run self exit).flatMap Effect4.Exit.causeReasons)

#check (@Effect4.FinalizerStrategy.cases_receipt :
  forall strategy : Effect4.FinalizerStrategy,
    strategy = Effect4.FinalizerStrategy.sequential \/
      strategy = Effect4.FinalizerStrategy.parallel)

#check (@Effect4.Scope.close_strategy_irrelevant :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (state : Effect4.ScopeState κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.close run
        ({ strategy := Effect4.FinalizerStrategy.parallel, state := state } :
          Effect4.Scope κ φ β ε δ ι α) exit).snd =
      (Effect4.Scope.close run
        ({ strategy := Effect4.FinalizerStrategy.sequential, state := state } :
          Effect4.Scope κ φ β ε δ ι α) exit).snd)

#check (@Effect4.Scope.closeResult_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.finalizers = [] -> Effect4.Scope.closeResult run self exit = Effect4.Exit.void)

#check (@Effect4.Scope.closeResult_single :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (key : κ)
    (finalizer : φ),
    self.isClosed = false -> self.finalizers = [(key, finalizer)] ->
      Effect4.Scope.closeResult run self exit = run finalizer exit)

#check (@Effect4.Scope.closeResult_many :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α)
    (first second : Effect4.Exit Unit ε δ ι α) (rest : List (Effect4.Exit Unit ε δ ι α)),
    self.isClosed = false ->
      Effect4.Scope.closeExits run self exit = first :: second :: rest ->
        Effect4.Scope.closeResult run self exit =
          Effect4.Exit.asVoidAll (first :: second :: rest))

#check (@Effect4.Scope.fork_closed_parent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) (exit : Effect4.Exit β ε δ ι α),
    parent.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.fork parent strategy key closeChild detachFromParent =
        (parent, ({ strategy := strategy, state := Effect4.ScopeState.closed exit } :
          Effect4.Scope κ φ β ε δ ι α)))

#check (@Effect4.Scope.fork_closed_parent_child_exit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) (exit : Effect4.Exit β ε δ ι α),
    parent.state = Effect4.ScopeState.closed exit ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.closingExit? =
        some exit)

#check (@Effect4.Scope.fork_open_parent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      Effect4.Scope.fork parent strategy key closeChild detachFromParent =
        (parent.addUnsafe key closeChild,
          (Effect4.Scope.make strategy :
            Effect4.Scope κ φ β ε δ ι α).addUnsafe key detachFromParent))

#check (@Effect4.Scope.fork_child_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.finalizers =
        [(key, detachFromParent)])

#check (@Effect4.Scope.fork_parent_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false -> key ∉ parent.finalizerKeys ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).fst.finalizers =
        parent.finalizers ++ [(key, closeChild)])

#check (@Effect4.Scope.fork_child_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.strategy =
      strategy)

#check (@Effect4.Scope.fork_shared_key :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      key ∈ (Effect4.Scope.fork parent strategy key closeChild
          detachFromParent).fst.finalizerKeys /\
        key ∈ (Effect4.Scope.fork parent strategy key closeChild
          detachFromParent).snd.finalizerKeys)

#check (@Effect4.Scope.fork_detach :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false -> key ∉ parent.finalizerKeys ->
      ((Effect4.Scope.fork parent strategy key closeChild
        detachFromParent).fst.removeUnsafe key).finalizers = parent.finalizers)

#check (@Effect4.Scope.addAll_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α), self.addAll [] = self)

#check (@Effect4.Scope.addAll_cons :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (entry : κ × φ) (rest : List (κ × φ)),
    self.addAll (entry :: rest) = (self.addUnsafe entry.fst entry.snd).addAll rest)

#check (@Effect4.Scope.addAll_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (registrations : List (κ × φ)),
    self.isClosed = false ->
      (self.finalizerKeys ++ registrations.map Prod.fst).Nodup ->
        (self.addAll registrations).finalizers = self.finalizers ++ registrations)

#check (@Effect4.Scope.make_addAll_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (strategy : Effect4.FinalizerStrategy) (registrations : List (κ × φ)),
    (registrations.map Prod.fst).Nodup ->
      ((Effect4.Scope.make strategy :
        Effect4.Scope κ φ β ε δ ι α).addAll registrations).finalizers = registrations)

#check (@Effect4.Scope.runScoped_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.runScoped run registrations bodyExit =
      Effect4.Scope.close run
        ((Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
          Effect4.Scope κ φ β ε δ ι α).addAll registrations) bodyExit)

#check (@Effect4.Scope.runScoped_fresh_scope :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
      Effect4.Scope κ φ β ε δ ι α) =
      { strategy := Effect4.FinalizerStrategy.sequential,
        state := Effect4.ScopeState.empty })

#check (@Effect4.Scope.runScoped_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.runScoped run registrations bodyExit).fst.state =
      Effect4.ScopeState.closed bodyExit)

#check (@Effect4.Scope.runScoped_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.runScoped run registrations bodyExit).fst.strategy =
      Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.runScoped_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (bodyExit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.runScoped run ([] : List (κ × φ)) bodyExit =
      (({ strategy := Effect4.FinalizerStrategy.sequential,
            state := Effect4.ScopeState.closed bodyExit } :
          Effect4.Scope κ φ β ε δ ι α),
        Effect4.Exit.void))

#check (@Effect4.Scope.acquireRelease_failure :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ)
    (cause : Effect4.Cause ε δ ι α),
    Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.failure cause) =
      (ambient, Effect4.Exit.void))

#check (@Effect4.Scope.acquireRelease_success :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β),
    Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.success value) =
      Effect4.Scope.addExit run ambient key release)

#check (@Effect4.Scope.acquireRelease_registers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β),
    ambient.isClosed = false -> key ∉ ambient.finalizerKeys ->
      (Effect4.Scope.acquireRelease run ambient key release
        (Effect4.Exit.success value)).fst.finalizers =
          ambient.finalizers ++ [(key, release)])

#check (@Effect4.Scope.acquireRelease_closed_ambient :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β)
    (exit : Effect4.Exit β ε δ ι α),
    ambient.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.success value) =
        (ambient, run release exit))


/-! Supervision controller receipts. Source interpretation remains open in
SUPERVISION-PG-RC112; every joined runtime row is partial. -/

#check (@Effect4.Supervision.MaskMode.select_interruptible :
  forall mask, Effect4.Supervision.MaskMode.select .interruptible mask = .unmasked)

#check (@Effect4.Supervision.MaskMode.select_uninterruptible :
  forall mask, Effect4.Supervision.MaskMode.select .uninterruptible mask = .masked)

#check (@Effect4.Supervision.MaskMode.select_inherit :
  forall mask, Effect4.Supervision.MaskMode.select .inherit mask = mask)

#check (@Effect4.Supervision.MaskMode.cases_receipt :
  forall mode : Effect4.Supervision.MaskMode, mode = .interruptible ∨ mode = .uninterruptible ∨ mode = .inherit)

#check (@Effect4.Supervision.ObserverMode.cases_receipt :
  forall mode : Effect4.Supervision.ObserverMode, mode = .awaitValue ∨ mode = .joinEffect)

#check (@Effect4.Supervision.ScopeMode.cases_receipt :
  forall mode : Effect4.Supervision.ScopeMode, mode = .forkIn ∨ mode = .fiberRunIn)

#check (@Effect4.Supervision.Globals.install_eq :
  forall g : Effect4.Supervision.Globals, Effect4.Supervision.Globals.install g = {g with middlewareInstalled := true})

#check (@Effect4.Supervision.Globals.valid_iff :
  forall g : Effect4.Supervision.Globals, Effect4.Supervision.Globals.Valid g ↔ g.allocated.Nodup)

#check (@Effect4.Supervision.Globals.ownsChildren_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (f : Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.Globals.OwnsChildren g f ↔ f.core.id ∈ g.allocated ∧ (∀ child, child ∈ f.children -> child ∈ g.allocated))

#check (@Effect4.Supervision.Fiber.valid_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.Valid f ↔ f.children.Nodup ∧ (f.subscriptions.map Effect4.Supervision.Subscription.key).Nodup ∧ (Effect4.FiberStatus.Active f.core.status -> f.core.terminal = none ∧ f.core.cleanup = .notStarted ∧ f.core.cleanupCount = 0) ∧ (f.core.status = .finalizing -> f.core.terminal.isSome = true ∧ f.core.cleanup = .pending ∧ f.core.cleanupCount = 0) ∧ (f.core.status = .done -> f.core.terminal.isSome = true ∧ f.core.cleanup = .done ∧ f.core.cleanupCount = 1))

#check (@Effect4.Supervision.Fiber.valid?_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.valid? f = true ↔ Effect4.Supervision.Fiber.Valid f)

#check (@Effect4.Supervision.Fiber.toFiberState_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.toFiberState f = f.core)

#check (@Effect4.Supervision.Fiber.published_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? f = some exit ↔ f.core.status = .done ∧ f.core.terminal = some exit)

#check (@Effect4.Supervision.Fiber.published_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Effect4.Supervision.Fiber χ β ε δ ι α, Effect4.Supervision.Fiber.published? f = if f.core.status = .done then f.core.terminal else none)

#check (@Effect4.Supervision.Fiber.addChild_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId), Effect4.Supervision.Fiber.addChild f child = {f with children := if child ∈ f.children then f.children else f.children ++ [child]})

#check (@Effect4.Supervision.Fiber.removeChild_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId), Effect4.Supervision.Fiber.removeChild f child = {f with children := f.children.filter (fun id => decide (id ≠ child))})

#check (@Effect4.Supervision.Fiber.addChild_nodup :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId), f.children.Nodup -> (Effect4.Supervision.Fiber.addChild f child).children.Nodup)

#check (@Effect4.Supervision.Fiber.removeChild_membership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (child other : Effect4.FiberId), other ∈ (Effect4.Supervision.Fiber.removeChild f child).children ↔ other ∈ f.children ∧ other ≠ child)

#check (@Effect4.Supervision.observation_await :
  forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, Effect4.Supervision.observation .awaitValue exit = .value exit)

#check (@Effect4.Supervision.observation_join :
  forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, Effect4.Supervision.observation .joinEffect exit = .effect exit)

#check (@Effect4.Supervision.observation_value_ne_effect :
  forall {β : Type v} {ε δ ι α : Type u}, forall exit : Effect4.Exit β ε δ ι α, (Effect4.Supervision.Observation.value exit : Effect4.Supervision.Observation β ε δ ι α) ≠ .effect exit)

#check (@Effect4.Supervision.Fiber.observe_invalid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription), Effect4.Supervision.Fiber.valid? f = false -> Effect4.Supervision.Fiber.observe f subscription = .error (.invalidFiber f.core.id))

#check (@Effect4.Supervision.Fiber.observe_done :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.Valid f -> Effect4.Supervision.Fiber.published? f = some exit -> Effect4.Supervision.Fiber.observe f subscription = .ok (f, Effect4.Supervision.observation subscription.mode exit))

#check (@Effect4.Supervision.Fiber.observe_live :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription), Effect4.Supervision.Fiber.Valid f -> Effect4.Supervision.Fiber.published? f = none -> subscription.key ∉ f.subscriptions.map Effect4.Supervision.Subscription.key -> Effect4.Supervision.Fiber.observe f subscription = .ok ({f with subscriptions := f.subscriptions ++ [subscription]}, .waiting subscription.key))

#check (@Effect4.Supervision.Fiber.observe_duplicate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (subscription : Effect4.Supervision.Subscription), Effect4.Supervision.Fiber.Valid f -> Effect4.Supervision.Fiber.published? f = none -> subscription.key ∈ f.subscriptions.map Effect4.Supervision.Subscription.key -> Effect4.Supervision.Fiber.observe f subscription = .error (.duplicateSubscription subscription.key))

#check (@Effect4.Supervision.Fiber.cancel_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (key : Nat), Effect4.Supervision.Fiber.cancel f key = {f with subscriptions := f.subscriptions.filter (fun subscription => decide (subscription.key ≠ key))})

#check (@Effect4.Supervision.Fiber.cancel_membership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (key : Nat) (subscription : Effect4.Supervision.Subscription), subscription ∈ (Effect4.Supervision.Fiber.cancel f key).subscriptions ↔ subscription ∈ f.subscriptions ∧ subscription.key ≠ key)

#check (@Effect4.Supervision.Fiber.publish_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.publish f exit = ({f with core := {f.core with status := .done, terminal := some exit, interruptPending := false, cleanup := .done, cleanupCount := 1}, children := [], subscriptions := []}, f.subscriptions.map (fun subscription => (subscription.key, Effect4.Supervision.observation subscription.mode exit))))

#check (@Effect4.Supervision.Fiber.publish_valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.Valid (Effect4.Supervision.Fiber.publish f exit).1)

#check (@Effect4.Supervision.interruptCause_eq :
  forall {ε δ ι α : Type u} (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α), (Effect4.Supervision.interruptCause encode requester annotations : Effect4.Cause ε δ ι α) = Effect4.Cause.annotate (Effect4.Cause.interrupt (requester.map encode)) annotations false)

#check (@Effect4.Supervision.Fiber.recordInterrupt_done :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? f = some exit -> Effect4.Supervision.Fiber.recordInterrupt encode requester annotations f = f)

#check (@Effect4.Supervision.Fiber.recordInterrupt_live :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.Fiber.published? f = none -> Effect4.Supervision.Fiber.recordInterrupt encode requester annotations f = {f with interrupted := some (match f.interrupted with | none => Effect4.Supervision.interruptCause encode requester annotations | some previous => Effect4.Cause.combine previous (Effect4.Supervision.interruptCause encode requester annotations))})

#check (@Effect4.Supervision.Fiber.recordInterrupt_core :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, [DecidableEq ε] -> [DecidableEq δ] -> [DecidableEq ι] -> [DecidableEq α] -> forall (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α) (f : Effect4.Supervision.Fiber χ β ε δ ι α), (Effect4.Supervision.Fiber.recordInterrupt encode requester annotations f).core = f.core)

#check (@Effect4.Supervision.initialFiber_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (mode : Effect4.Supervision.MaskMode), Effect4.Supervision.initialFiber parent child mode = { core := {id := child, status := .runnable, terminal := none, mask := Effect4.Supervision.MaskMode.select mode parent.core.mask, interruptPending := false, cleanup := .notStarted, cleanupCount := 0}, context := parent.context, children := [], subscriptions := [], interrupted := none })

#check (@Effect4.Supervision.initialFiber_valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (mode : Effect4.Supervision.MaskMode), Effect4.Supervision.Fiber.Valid (Effect4.Supervision.initialFiber parent child mode))

#check (@Effect4.Supervision.commitFork_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent initial child : Effect4.Supervision.Fiber χ β ε δ ι α) (daemon : Bool) (events : List Effect4.Supervision.ForkEvent), Effect4.Supervision.commitFork g parent initial child daemon events = { globals := g, parent := if daemon = false ∧ Effect4.Supervision.Fiber.published? child = none then Effect4.Supervision.Fiber.addChild parent child.core.id else parent, initial := initial, child := child, events := events ++ (if daemon = false ∧ Effect4.Supervision.Fiber.published? child = none then [.registered parent.core.id child.core.id] else []), removeFromParent := if daemon = false ∧ Effect4.Supervision.Fiber.published? child = none then some parent.core.id else none })

#check (@Effect4.Supervision.forkUnsafe_duplicate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α), child ∈ g.allocated -> Effect4.Supervision.forkUnsafe g parent child options start = .error (.duplicateFiber child))

#check (@Effect4.Supervision.forkUnsafe_deferred :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) , child ∉ g.allocated -> options.startImmediately = false -> Effect4.Supervision.forkUnsafe g parent child options .deferred = .ok (Effect4.Supervision.commitFork (Effect4.Supervision.Globals.allocate g child) parent (Effect4.Supervision.initialFiber parent child options.maskMode) (Effect4.Supervision.initialFiber parent child options.maskMode) options.daemon [.scheduled child 0]))

#check (@Effect4.Supervision.forkUnsafe_wrong_deferred :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) , child ∉ g.allocated -> options.startImmediately = true -> Effect4.Supervision.forkUnsafe g parent child options .deferred = .error .wrongStartMode)

#check (@Effect4.Supervision.forkUnsafe_wrong_immediate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongStartMode)

#check (@Effect4.Supervision.forkUnsafe_wrong_identity :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id ≠ child -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongChildIdentity)

#check (@Effect4.Supervision.forkUnsafe_wrong_parent :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id ≠ parent.core.id -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .wrongParentIdentity)

#check (@Effect4.Supervision.forkUnsafe_invalid_child :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.valid? after = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error (.invalidFiber child))

#check (@Effect4.Supervision.forkUnsafe_invalid_parent :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.valid? postParent = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error (.invalidFiber parent.core.id))

#check (@Effect4.Supervision.forkUnsafe_invalid_globals :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.extends? (Effect4.Supervision.Globals.allocate g child) postGlobals = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidStartGlobals)

#check (@Effect4.Supervision.forkUnsafe_invalid_ownership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.Extends (Effect4.Supervision.Globals.allocate g child) postGlobals -> Effect4.Supervision.Globals.ownsChildren? postGlobals postParent = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidParentOwnership)

#check (@Effect4.Supervision.forkUnsafe_invalid_child_ownership :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.Extends (Effect4.Supervision.Globals.allocate g child) postGlobals -> Effect4.Supervision.Globals.OwnsChildren postGlobals postParent -> Effect4.Supervision.Globals.ownsChildren? postGlobals after = false -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .error .invalidChildOwnership)

#check (@Effect4.Supervision.forkUnsafe_immediate :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (postGlobals : Effect4.Supervision.Globals) (postParent after : Effect4.Supervision.Fiber χ β ε δ ι α), child ∉ g.allocated -> options.startImmediately = true -> after.core.id = child -> postParent.core.id = parent.core.id -> Effect4.Supervision.Fiber.Valid after -> Effect4.Supervision.Fiber.Valid postParent -> Effect4.Supervision.Globals.Extends (Effect4.Supervision.Globals.allocate g child) postGlobals -> Effect4.Supervision.Globals.OwnsChildren postGlobals postParent -> Effect4.Supervision.Globals.OwnsChildren postGlobals after -> Effect4.Supervision.forkUnsafe g parent child options (.immediate postGlobals postParent after) = .ok (Effect4.Supervision.commitFork postGlobals postParent (Effect4.Supervision.initialFiber parent child options.maskMode) after options.daemon [.evaluated child]))

#check (@Effect4.Supervision.forkUnsafe_fresh :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> child ∉ g.allocated)

#check (@Effect4.Supervision.forkUnsafe_allocated_nodup :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), Effect4.Supervision.Globals.Valid g -> Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> Effect4.Supervision.Globals.Valid result.globals)

#check (@Effect4.Supervision.forkUnsafe_child_valid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> Effect4.Supervision.Fiber.Valid result.child)

#check (@Effect4.Supervision.forkUnsafe_parent_children_nodup :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α) (result : Effect4.Supervision.ForkResult χ β ε δ ι α), parent.children.Nodup -> Effect4.Supervision.forkUnsafe g parent child options start = .ok result -> result.parent.children.Nodup)

#check (@Effect4.Supervision.forkChild_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α), Effect4.Supervision.forkChild g parent child options start = Effect4.Supervision.forkUnsafe (Effect4.Supervision.Globals.install g) parent child {options with daemon := false} start)

#check (@Effect4.Supervision.forkDetach_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (child : Effect4.FiberId) (options : Effect4.Supervision.ForkOptions) (start : Effect4.Supervision.StartObservation χ β ε δ ι α), Effect4.Supervision.forkDetach g parent child options start = Effect4.Supervision.forkUnsafe g parent child {options with daemon := true} start)

#check (@Effect4.Supervision.commitFork_done_untracked :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent initial child : Effect4.Supervision.Fiber χ β ε δ ι α) (daemon : Bool) (events : List Effect4.Supervision.ForkEvent) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? child = some exit -> (Effect4.Supervision.commitFork g parent initial child daemon events).parent = parent ∧ (Effect4.Supervision.commitFork g parent initial child daemon events).removeFromParent = none ∧ (Effect4.Supervision.commitFork g parent initial child daemon events).events = events)

#check (@Effect4.Supervision.commitFork_daemon_untracked :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent initial child : Effect4.Supervision.Fiber χ β ε δ ι α) (events : List Effect4.Supervision.ForkEvent), (Effect4.Supervision.commitFork g parent initial child true events).parent = parent ∧ (Effect4.Supervision.commitFork g parent initial child true events).removeFromParent = none ∧ (Effect4.Supervision.commitFork g parent initial child true events).events = events)

#check (@Effect4.Supervision.Globals.allocate_eq :
  forall (g : Effect4.Supervision.Globals) (child : Effect4.FiberId), Effect4.Supervision.Globals.allocate g child = {g with allocated := g.allocated ++ [child]})

#check (@Effect4.Supervision.Globals.extends_iff :
  forall before after : Effect4.Supervision.Globals, Effect4.Supervision.Globals.Extends before after ↔ after.allocated.take before.allocated.length = before.allocated ∧ (before.middlewareInstalled = true -> after.middlewareInstalled = true) ∧ after.allocated.Nodup)

#check (@Effect4.Supervision.Globals.extends?_iff :
  forall before after : Effect4.Supervision.Globals, Effect4.Supervision.Globals.extends? before after = true ↔ Effect4.Supervision.Globals.Extends before after)

#check (@Effect4.Supervision.Globals.ownsChildren?_iff :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (f : Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.Globals.ownsChildren? g f = true ↔ Effect4.Supervision.Globals.OwnsChildren g f)

#check (@Effect4.Supervision.WaitState.begin_eq :
  forall {τ : Type u}, forall (targets : List Effect4.FiberId) (result : τ), Effect4.Supervision.WaitState.begin targets result = {targets := targets, published := [], result := result})

#check (@Effect4.Supervision.WaitState.pending_eq :
  forall {τ : Type u}, forall s : Effect4.Supervision.WaitState τ, Effect4.Supervision.WaitState.pending s = s.targets.filter (fun id => decide (id ∉ s.published)))

#check (@Effect4.Supervision.WaitState.ready_iff :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (result : τ), Effect4.Supervision.WaitState.ready? s = some result ↔ Effect4.Supervision.WaitState.pending s = [] ∧ s.result = result)

#check (@Effect4.Supervision.WaitState.ready_publications :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (result : τ), Effect4.Supervision.WaitState.ready? s = some result -> ∀ child, child ∈ s.targets -> child ∈ s.published)

#check (@Effect4.Supervision.WaitState.observe_pending :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId), child ∈ Effect4.Supervision.WaitState.pending s -> Effect4.Supervision.WaitState.observe s child = .ok {s with published := s.published ++ [child]})

#check (@Effect4.Supervision.WaitState.observe_unknown :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId), child ∉ Effect4.Supervision.WaitState.pending s -> Effect4.Supervision.WaitState.observe s child = .error (.unknownPublication child))

#check (@Effect4.Supervision.WaitState.observe_pending_membership :
  forall {τ : Type u}, forall (s after : Effect4.Supervision.WaitState τ) (child other : Effect4.FiberId), Effect4.Supervision.WaitState.observe s child = .ok after -> (other ∈ Effect4.Supervision.WaitState.pending after ↔ other ∈ Effect4.Supervision.WaitState.pending s ∧ other ≠ child))

#check (@Effect4.Supervision.waitStep_iff :
  forall {τ : Type u}, forall (before after : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId), Effect4.Supervision.WaitStep before child after ↔ Effect4.Supervision.WaitState.observe before child = .ok after)

#check (@Effect4.Supervision.waitRuns_iff :
  forall {τ : Type u}, forall (initial : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId) (result : Effect4.Supervision.ReplayResult (Effect4.Supervision.WaitState τ) τ), Effect4.Supervision.WaitRuns initial tape result ↔ result = Effect4.Supervision.waitReplay initial tape)

#check (@Effect4.Supervision.ReplayResult.state_done :
  forall {σ : Type u} {τ : Type v} (state : σ) (result : τ), Effect4.Supervision.ReplayResult.state (Effect4.Supervision.ReplayResult.done state result) = state)

#check (@Effect4.Supervision.ReplayResult.state_frontier :
  forall {σ : Type u} {τ : Type v} (state : σ), Effect4.Supervision.ReplayResult.state (Effect4.Supervision.ReplayResult.frontier state : Effect4.Supervision.ReplayResult σ τ) = state)

#check (@Effect4.Supervision.ReplayResult.state_refused :
  forall {σ : Type u} {τ : Type v} (state : σ) (reason : Effect4.Supervision.Refusal), Effect4.Supervision.ReplayResult.state (Effect4.Supervision.ReplayResult.refused state reason : Effect4.Supervision.ReplayResult σ τ) = state)

#check (@Effect4.Supervision.waitReplay_ready :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (result : τ) (tape : List Effect4.FiberId), Effect4.Supervision.WaitState.ready? s = some result -> Effect4.Supervision.waitReplay s tape = .done s result)

#check (@Effect4.Supervision.waitReplay_frontier :
  forall {τ : Type u}, forall s : Effect4.Supervision.WaitState τ, Effect4.Supervision.WaitState.ready? s = none -> Effect4.Supervision.waitReplay s [] = .frontier s)

#check (@Effect4.Supervision.waitReplay_cons_ok :
  forall {τ : Type u}, forall (s after : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId) (tape : List Effect4.FiberId), Effect4.Supervision.WaitState.ready? s = none -> Effect4.Supervision.WaitState.observe s child = .ok after -> Effect4.Supervision.waitReplay s (child :: tape) = Effect4.Supervision.waitReplay after tape)

#check (@Effect4.Supervision.waitReplay_cons_error :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (child : Effect4.FiberId) (tape : List Effect4.FiberId) (reason : Effect4.Supervision.Refusal), Effect4.Supervision.WaitState.ready? s = none -> Effect4.Supervision.WaitState.observe s child = .error reason -> Effect4.Supervision.waitReplay s (child :: tape) = .refused s reason)

#check (@Effect4.Supervision.wait_fixedTape_deterministic :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId) (left right : Effect4.Supervision.ReplayResult (Effect4.Supervision.WaitState τ) τ), Effect4.Supervision.WaitRuns s tape left -> Effect4.Supervision.WaitRuns s tape right -> left = right)

#check (@Effect4.Supervision.waitReplay_done_ready :
  forall {τ : Type u}, forall (s after : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId) (result : τ), Effect4.Supervision.waitReplay s tape = .done after result -> Effect4.Supervision.WaitState.ready? after = some result)

#check (@Effect4.Supervision.waitReplay_frame :
  forall {τ : Type u}, forall (s : Effect4.Supervision.WaitState τ) (tape : List Effect4.FiberId), let after := Effect4.Supervision.ReplayResult.state (Effect4.Supervision.waitReplay s tape); after.targets = s.targets ∧ after.result = s.result ∧ (∀ child, child ∈ after.published -> child ∈ s.published ++ tape))

#check (@Effect4.Supervision.wait_two_publications :
  forall {τ : Type u}, forall (left right : Effect4.FiberId) (result : τ), left ≠ right -> Effect4.Supervision.waitReplay (Effect4.Supervision.WaitState.begin [left, right] result) [left, right] = .done {targets := [left, right], published := [left, right], result := result} result)

#check (@Effect4.Supervision.beginParentExit_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (g : Effect4.Supervision.Globals) (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.beginParentExit g parent exit = Effect4.Supervision.WaitState.begin (if g.middlewareInstalled then parent.children else []) exit)

#check (@Effect4.Supervision.parentExitView_waiting :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)), Effect4.Supervision.WaitState.ready? wait = none -> Effect4.Supervision.parentExitView parent wait = {parent with core := {parent.core with status := .finalizing, terminal := some wait.result, interruptPending := false, cleanup := .pending, cleanupCount := 0}, children := Effect4.Supervision.WaitState.pending wait})

#check (@Effect4.Supervision.parentExitView_ready :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.WaitState.ready? wait = some exit -> Effect4.Supervision.parentExitView parent wait = (Effect4.Supervision.Fiber.publish parent exit).1)

#check (@Effect4.Supervision.parentExitView_not_published_while_waiting :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)), Effect4.Supervision.WaitState.ready? wait = none -> Effect4.Supervision.Fiber.published? (Effect4.Supervision.parentExitView parent wait) = none)

#check (@Effect4.Supervision.parentExitView_publication_requires_children :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.Supervision.Fiber χ β ε δ ι α) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.published? (Effect4.Supervision.parentExitView parent wait) = some exit -> ∀ child, child ∈ wait.targets -> child ∈ wait.published)

#check (@Effect4.Supervision.newChildren_eq :
  forall initial current : List Effect4.FiberId, Effect4.Supervision.newChildren initial current = current.filter (fun child => decide (child ∉ initial)))

#check (@Effect4.Supervision.newChildren_membership :
  forall (initial current : List Effect4.FiberId) (child : Effect4.FiberId), child ∈ Effect4.Supervision.newChildren initial current ↔ child ∈ current ∧ child ∉ initial)

#check (@Effect4.Supervision.awaitAllChildren_eq :
  forall initial current : List Effect4.FiberId, Effect4.Supervision.awaitAllChildren initial current = Effect4.Supervision.WaitState.begin (Effect4.Supervision.newChildren initial current) ())

#check (@Effect4.Supervision.interruptAllRequests_eq :
  forall targets : List Effect4.FiberId, Effect4.Supervision.interruptAllRequests targets = targets.map Effect4.Supervision.InterruptAction.request ++ [.awaitAll targets])

#check (@Effect4.Supervision.interruptAllWait_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall fibers : List (Effect4.Supervision.Fiber χ β ε δ ι α), Effect4.Supervision.interruptAllWait fibers = {targets := fibers.map (fun f => f.core.id), published := (fibers.filter (fun f => (Effect4.Supervision.Fiber.published? f).isSome)).map (fun f => f.core.id), result := ()})

#check (@Effect4.Supervision.bindScope_invalid :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.valid? child = false -> Effect4.Supervision.bindScope mode parent child scope key = .error (.invalidFiber child.core.id))

#check (@Effect4.Supervision.bindScope_done :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = some exit -> Effect4.Supervision.bindScope mode parent child scope key = .ok {scope := scope, observerKey := none, interruptor := none})

#check (@Effect4.Supervision.bindScope_closed :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = none -> scope.isClosed = true -> Effect4.Supervision.bindScope mode parent child scope key = .ok {scope := scope, observerKey := none, interruptor := some (if mode = .forkIn then parent else child.core.id)})

#check (@Effect4.Supervision.bindScope_duplicate_key :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = none -> scope.isClosed = false -> (ULift.up key : ULift.{u} Nat) ∈ scope.finalizerKeys -> Effect4.Supervision.bindScope mode parent child scope key = .error (.duplicateScopeKey key))

#check (@Effect4.Supervision.bindScope_open :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (mode : Effect4.Supervision.ScopeMode) (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat) , Effect4.Supervision.Fiber.Valid child -> Effect4.Supervision.Fiber.published? child = none -> scope.isClosed = false -> (ULift.up key : ULift.{u} Nat) ∉ scope.finalizerKeys -> Effect4.Supervision.bindScope mode parent child scope key = .ok {scope := scope.addUnsafe (ULift.up key) (ULift.up {child := child.core.id, skipSelf := decide (mode = .forkIn)}), observerKey := some key, interruptor := none})

#check (@Effect4.Supervision.forkScopedBinding_eq :
  forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall (parent : Effect4.FiberId) (child : Effect4.Supervision.Fiber χ β ε δ ι α) (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat), Effect4.Supervision.forkScopedBinding parent child scope key = Effect4.Supervision.bindScope .forkIn parent child scope key)

#check (@Effect4.Supervision.scopeFinalizerInterruptor_eq :
  forall (finalizer : Effect4.Supervision.ScopeFinalizer) (current : Effect4.FiberId), Effect4.Supervision.scopeFinalizerInterruptor finalizer current = if finalizer.skipSelf = true ∧ current = finalizer.child then none else some current)

#check (@Effect4.Supervision.scopeFinalizer_self_guard :
  forall child : Effect4.FiberId, Effect4.Supervision.scopeFinalizerInterruptor {child := child, skipSelf := true} child = none ∧ Effect4.Supervision.scopeFinalizerInterruptor {child := child, skipSelf := false} child = some child)

#check (@Effect4.Supervision.scopeObserver_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key : Nat), Effect4.Supervision.scopeObserver scope key = scope.removeUnsafe (ULift.up key))

#check (@Effect4.Supervision.scopeObserver_key_membership :
  forall {β : Type v} {ε δ ι α : Type u}, forall (scope : Effect4.Scope (ULift.{u} Nat) (ULift.{u} Effect4.Supervision.ScopeFinalizer) β ε δ ι α) (key other : Nat), (ULift.up other : ULift.{u} Nat) ∈ (Effect4.Supervision.scopeObserver scope key).finalizerKeys ↔ (ULift.up other : ULift.{u} Nat) ∈ scope.finalizerKeys ∧ other ≠ key)

#check (@Effect4.Supervision.raceForkOptions_eq :
  Effect4.Supervision.raceForkOptions = {startImmediately := true, daemon := true, maskMode := .interruptible})

#check (@Effect4.Supervision.raceCleanupMask_eq :
  Effect4.Supervision.raceCleanupMask = Effect4.InterruptMask.masked)

#check (@Effect4.Supervision.RaceAllState.initial_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (Effect4.Supervision.RaceAllState.initial entrants : Effect4.Supervision.RaceAllState β ε δ ι α) = {unstarted := entrants, starting := none, live := [], remaining := entrants.length, failures := [], winner := none, accepted := none, cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false})

#check (@Effect4.Supervision.raceAllAdmit_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (Effect4.Supervision.raceAllAdmit entrants : Except Effect4.Supervision.Refusal (Effect4.Supervision.RaceAllState β ε δ ι α)) = if entrants.Nodup then .ok (Effect4.Supervision.RaceAllState.initial entrants) else .error .duplicateEntrant)

#check (@Effect4.Supervision.RaceAllState.result_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, Effect4.Supervision.RaceAllState.result? s = if s.starting.isSome then none else if s.cleanupNeeded = false then s.accepted else if s.cleanupRequested = true ∧ (s.cleanup.bind Effect4.Supervision.WaitState.ready?).isSome = true then s.accepted else none)

#check (@Effect4.Supervision.raceComplete_unknown :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> Effect4.Supervision.raceComplete s child exit = s)

#check (@Effect4.Supervision.raceComplete_after_accepted :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit accepted : Effect4.Exit β ε δ ι α), child ∈ s.live -> s.accepted = some accepted -> Effect4.Supervision.raceComplete s child exit = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait => if child ∈ Effect4.Supervision.WaitState.pending wait then {wait with published := wait.published ++ [child]} else wait)})

#check (@Effect4.Supervision.raceComplete_success :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (value : β), child ∈ s.live -> s.accepted = none -> Effect4.Supervision.raceComplete s child (.success value) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !(s.live.filter (fun id => decide (id ≠ child))).isEmpty, requests := [], cleanup := none, cleanupRequested := false})

#check (@Effect4.Supervision.raceComplete_failure_last :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> s.remaining ≤ 1 -> Effect4.Supervision.raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false})

#check (@Effect4.Supervision.raceComplete_failure_pending :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> 1 < s.remaining -> Effect4.Supervision.raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons})

#check (@Effect4.Supervision.raceStep_begin_blocked :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.accepted.isSome = true ∨ s.starting.isSome = true -> Effect4.Supervision.raceStep s .beginLaunch = .error .wrongRacePhase)

#check (@Effect4.Supervision.raceStep_begin_empty :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.accepted = none -> s.starting = none -> s.unstarted = [] -> Effect4.Supervision.raceStep s .beginLaunch = .error .noEntrant)

#check (@Effect4.Supervision.raceStep_begin :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (rest : List Effect4.FiberId), s.accepted = none -> s.starting = none -> s.unstarted = child :: rest -> Effect4.Supervision.raceStep s .beginLaunch = .ok {s with unstarted := rest, starting := some child})

#check (@Effect4.Supervision.raceStep_finish_missing :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Option (Effect4.Exit β ε δ ι α)), s.starting = none -> Effect4.Supervision.raceStep s (.finishLaunch exit) = .error .wrongRacePhase)

#check (@Effect4.Supervision.raceStep_finish_duplicate :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Option (Effect4.Exit β ε δ ι α)), s.starting = some child -> child ∈ s.live -> Effect4.Supervision.raceStep s (.finishLaunch exit) = .error .duplicateEntrant)

#check (@Effect4.Supervision.raceStep_finish_live :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId), s.starting = some child -> child ∉ s.live -> Effect4.Supervision.raceStep s (.finishLaunch none) = .ok {s with starting := none, live := s.live ++ [child]})

#check (@Effect4.Supervision.raceStep_finish_done :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), s.starting = some child -> child ∉ s.live -> Effect4.Supervision.raceStep s (.finishLaunch (some exit)) = .ok (Effect4.Supervision.raceComplete {s with starting := none, live := s.live ++ [child]} child exit))

#check (@Effect4.Supervision.raceStep_complete :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∈ s.live -> Effect4.Supervision.raceStep s (.complete child exit) = .ok (Effect4.Supervision.raceComplete s child exit))

#check (@Effect4.Supervision.raceStep_complete_unknown :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> Effect4.Supervision.raceStep s (.complete child exit) = .error (.unknownEntrant child))

#check (@Effect4.Supervision.raceStep_beginCleanup :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), s.starting = none -> s.accepted = some exit -> s.cleanupNeeded = true -> s.cleanup = none -> Effect4.Supervision.raceStep s .beginCleanup = .ok {s with requests := s.live, cleanup := some (Effect4.Supervision.WaitState.begin s.live exit), cleanupRequested := s.live.isEmpty})

#check (@Effect4.Supervision.raceStep_beginCleanup_blocked :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.starting.isSome = true ∨ s.accepted = none ∨ s.cleanupNeeded = false ∨ s.cleanup.isSome = true -> Effect4.Supervision.raceStep s .beginCleanup = .error .wrongRacePhase)

#check (@Effect4.Supervision.raceStep_requestNext :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (rest : List Effect4.FiberId) (wait : Effect4.Supervision.WaitState (Effect4.Exit β ε δ ι α)), s.cleanup = some wait -> s.cleanupRequested = false -> s.requests = child :: rest -> Effect4.Supervision.raceStep s .requestNext = .ok {s with requests := rest, cleanupRequested := rest.isEmpty})

#check (@Effect4.Supervision.raceStep_requestNext_blocked :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, s.cleanup = none ∨ s.cleanupRequested = true ∨ s.requests = [] -> Effect4.Supervision.raceStep s .requestNext = .error .wrongRacePhase)

#check (@Effect4.Supervision.raceStep_iff :
  forall {β : Type v} {ε δ ι α : Type u}, forall (before after : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α), Effect4.Supervision.RaceStep before decision after ↔ Effect4.Supervision.raceStep before decision = .ok after)

#check (@Effect4.Supervision.raceRuns_iff :
  forall {β : Type v} {ε δ ι α : Type u}, forall (initial : Effect4.Supervision.RaceAllState β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)) (result : Effect4.Supervision.ReplayResult (Effect4.Supervision.RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α)), Effect4.Supervision.RaceRuns initial tape result ↔ result = Effect4.Supervision.raceReplay initial tape)

#check (@Effect4.Supervision.raceReplay_ready :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)), Effect4.Supervision.RaceAllState.result? s = some exit -> Effect4.Supervision.raceReplay s tape = .done s exit)

#check (@Effect4.Supervision.raceReplay_frontier :
  forall {β : Type v} {ε δ ι α : Type u}, forall s : Effect4.Supervision.RaceAllState β ε δ ι α, Effect4.Supervision.RaceAllState.result? s = none -> Effect4.Supervision.raceReplay s [] = .frontier s)

#check (@Effect4.Supervision.raceReplay_cons_ok :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s after : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)), Effect4.Supervision.RaceAllState.result? s = none -> Effect4.Supervision.raceStep s decision = .ok after -> Effect4.Supervision.raceReplay s (decision :: tape) = Effect4.Supervision.raceReplay after tape)

#check (@Effect4.Supervision.raceReplay_cons_error :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)) (reason : Effect4.Supervision.Refusal), Effect4.Supervision.RaceAllState.result? s = none -> Effect4.Supervision.raceStep s decision = .error reason -> Effect4.Supervision.raceReplay s (decision :: tape) = .refused s reason)

#check (@Effect4.Supervision.race_fixedTape_deterministic :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (tape : List (Effect4.Supervision.RaceAllDecision β ε δ ι α)) (left right : Effect4.Supervision.ReplayResult (Effect4.Supervision.RaceAllState β ε δ ι α) (Effect4.Exit β ε δ ι α)), Effect4.Supervision.RaceRuns s tape left -> Effect4.Supervision.RaceRuns s tape right -> left = right)

#check (@Effect4.Supervision.race_first_accepted_stable :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s after : Effect4.Supervision.RaceAllState β ε δ ι α) (decision : Effect4.Supervision.RaceAllDecision β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), s.accepted = some exit -> Effect4.Supervision.raceStep s decision = .ok after -> after.accepted = some exit)

#check (@Effect4.Supervision.race_result_requires_start_finished :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.RaceAllState.result? s = some exit -> s.starting = none ∧ s.accepted = some exit)

#check (@Effect4.Supervision.race_cleanup_result_requires_publications :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Supervision.RaceAllState.result? s = some exit -> s.cleanupNeeded = true -> s.cleanupRequested = true ∧ ∃ wait, s.cleanup = some wait ∧ ∀ child, child ∈ wait.targets -> child ∈ wait.published)

#check (@Effect4.Supervision.race_empty_frontier :
  forall {β : Type v} {ε δ ι α : Type u}, Effect4.Supervision.raceReplay (Effect4.Supervision.RaceAllState.initial [] : Effect4.Supervision.RaceAllState β ε δ ι α) [] = .frontier (Effect4.Supervision.RaceAllState.initial []))

#check (@Effect4.Supervision.race_single_success :
  forall {β : Type v} {ε δ ι α : Type u}, forall (child : Effect4.FiberId) (value : β), ∃ after, Effect4.Supervision.raceReplay (Effect4.Supervision.RaceAllState.initial [child] : Effect4.Supervision.RaceAllState β ε δ ι α) [.beginLaunch, .finishLaunch (some (.success value))] = .done after (.success value))

#check (@Effect4.Supervision.race_two_failures :
  forall {β : Type v} {ε δ ι α : Type u}, forall (left right : Effect4.FiberId) (first second : Effect4.Cause ε δ ι α), left ≠ right -> ∃ after, Effect4.Supervision.raceReplay (Effect4.Supervision.RaceAllState.initial [left, right] : Effect4.Supervision.RaceAllState β ε δ ι α) [.beginLaunch, .finishLaunch (some (.failure first)), .beginLaunch, .finishLaunch (some (.failure second))] = .done after (.failure ⟨first.reasons ++ second.reasons⟩))

/-! The frame-machine witnesses. Statements are transcribed from the frozen
ascriptions of `Effect4Test/Runtime/FramesContract.lean`.

The `Effect4.Prim` and `Effect4.FrameFiber` telescopes carry seven type
parameters, and many of these statements quantify over all seven while naming
only some. The binder names are part of the frozen statement, so they are
transcribed as written rather than renamed to `_ν` to please the
unused-variable linter; the option below is scoped to this section. -/

set_option linter.unusedVariables false

#check (@Effect4.Arm.all_nodup : List.Nodup Effect4.Arm.all)

#check (@Effect4.Arm.mem_all : ∀ (arm : Effect4.Arm), arm ∈ Effect4.Arm.all)

#check (@Effect4.Arm.cases_receipt :
  ∀ (arm : Effect4.Arm), arm = Effect4.Arm.contA ∨ arm = Effect4.Arm.contE ∨ arm =
  Effect4.Arm.contAll)

#check (@Effect4.Arm.demandable_eq :
  Effect4.Arm.demandable = [Effect4.Arm.contA, Effect4.Arm.contE])

#check (@Effect4.Arm.contAll_not_demandable : ¬Effect4.Arm.contAll ∈ Effect4.Arm.demandable)

#check (@Effect4.Prim.cases_receipt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α), (∃
  value, self = Effect4.Prim.success value) ∨ (∃ cause, self = Effect4.Prim.failure cause) ∨ (∃
  thunk, self = Effect4.Prim.sync thunk) ∨ (∃ thunk, self = Effect4.Prim.suspend thunk) ∨ (∃
  thunk, self = Effect4.Prim.withFiber thunk) ∨ (∃ error, self = Effect4.Prim.yieldableError
  error) ∨ (∃ generator cursor, self = Effect4.Prim.iterator generator cursor) ∨ (∃ body
  onValue, self = Effect4.Prim.onSuccess body onValue) ∨ (∃ body onCause, self =
  Effect4.Prim.onFailure body onCause) ∨ (∃ body onValue onCause, self =
  Effect4.Prim.onSuccessAndFailure body onValue onCause) ∨ (∃ body, self =
  Effect4.Prim.exitFrame body) ∨ (∃ body finalizer flag, self = Effect4.Prim.onExit body
  finalizer flag) ∨ (∃ flag, self = Effect4.Prim.setInterruptible flag) ∨ (∃ loop cursor, self =
  Effect4.Prim.whileLoop loop cursor) ∨ (∃ priority, self = Effect4.Prim.yieldNowWith priority)
  ∨ (∃ register withSignal cancel, self = Effect4.Prim.async register withSignal cancel) ∨ ∃
  onInterrupt, self = Effect4.Prim.asyncFinalizer onInterrupt)

#check (@Effect4.FrameFiber.start_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (current : Effect4.Prim ν σ β ε δ ι α),
  Effect4.FrameFiber.start current = Effect4.FrameFiber.mk current [] Bool.true Option.none
  Bool.false)

#check (@Effect4.FrameFiber.pendingCause_some :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (cause : Effect4.Cause ε δ ι α), self.interruptedCause = Option.some cause →
  Effect4.FrameFiber.pendingCause self = cause)

#check (@Effect4.FrameFiber.pendingCause_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptedCause = Option.none → Effect4.FrameFiber.pendingCause self =
  Effect4.Cause.empty)

#check (@Effect4.FrameFiber.masked_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.masked self = !self.interruptible)

#check (@Effect4.FrameFiber.interrupted_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.interrupted self = (self.interruptible && Option.isSome
  self.interruptedCause))

#check (@Effect4.FrameEvent.poppedFrames_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FrameEvent.poppedFrames [] = [])

#check (@Effect4.FrameEvent.poppedFrames_cons_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (rest :
  List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.poppedFrames
  (Effect4.FrameEvent.popped frame :: rest) = frame :: Effect4.FrameEvent.poppedFrames rest)

#check (@Effect4.FrameEvent.finalizersRun_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FrameEvent.finalizersRun [] = [])

#check (@Effect4.FrameEvent.finalizersRun_cons_ran :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (finalizer : ν) (exit : Effect4.Exit β ε δ ι
  α) (rest : List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.finalizersRun
  (Effect4.FrameEvent.ranFinalizer finalizer exit :: rest) = finalizer ::
  Effect4.FrameEvent.finalizersRun rest)

#check (@Effect4.FrameEvent.finalizersRun_cons_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (rest :
  List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.finalizersRun
  (Effect4.FrameEvent.popped frame :: rest) = Effect4.FrameEvent.finalizersRun rest)

#check (@Effect4.Prim.hasArm_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α) (arm :
  Effect4.Arm), Effect4.Prim.hasArm self arm = List.contains (Effect4.Prim.arms self) arm)

#check (@Effect4.Prim.isFrame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.isFrame self = !List.isEmpty (Effect4.Prim.arms self))

#check (@Effect4.Prim.isFrame_iff :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.isFrame self = Bool.true ↔ Effect4.Prim.arms self ≠ [])

#check (@Effect4.Prim.arms_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  : ν), Effect4.Prim.arms (Effect4.Prim.onSuccess body onValue) = [Effect4.Arm.contA])

#check (@Effect4.Prim.arms_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onCause
  : ν), Effect4.Prim.arms (Effect4.Prim.onFailure body onCause) = [Effect4.Arm.contE])

#check (@Effect4.Prim.arms_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  onCause : ν), Effect4.Prim.arms (Effect4.Prim.onSuccessAndFailure body onValue onCause) =
  [Effect4.Arm.contA, Effect4.Arm.contE])

#check (@Effect4.Prim.arms_exitFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.arms (Effect4.Prim.exitFrame body) = [Effect4.Arm.contA, Effect4.Arm.contE])

#check (@Effect4.Prim.arms_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool), Effect4.Prim.arms (Effect4.Prim.onExit body finalizer flag) =
  [Effect4.Arm.contA, Effect4.Arm.contE, Effect4.Arm.contAll])

#check (@Effect4.Prim.arms_setInterruptible :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool), Effect4.Prim.arms
  (Effect4.Prim.setInterruptible flag) = [Effect4.Arm.contAll])

#check (@Effect4.Prim.arms_whileLoop :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (loop : ν) (cursor : β), Effect4.Prim.arms
  (Effect4.Prim.whileLoop loop cursor) = [Effect4.Arm.contA])

#check (@Effect4.Prim.arms_iterator :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (generator : ν) (cursor : β),
  Effect4.Prim.arms (Effect4.Prim.iterator generator cursor) = [Effect4.Arm.contA])

#check (@Effect4.Prim.non_frames_have_no_arms :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (value : β) (cause : Effect4.Cause ε δ ι α)
  (thunk : σ) (error : ε) (priority : Nat) (register : ν) (withSignal : Bool) (cancel : Option
  ν), Effect4.Prim.arms (Effect4.Prim.success value) = [] ∧
  Effect4.Prim.arms (Effect4.Prim.failure cause) = [] ∧ Effect4.Prim.arms (Effect4.Prim.sync
  thunk) = [] ∧ Effect4.Prim.arms (Effect4.Prim.suspend thunk) = [] ∧ Effect4.Prim.arms
  (Effect4.Prim.withFiber thunk) = [] ∧ Effect4.Prim.arms (Effect4.Prim.yieldableError error) =
  [] ∧ Effect4.Prim.arms (Effect4.Prim.yieldNowWith priority) = [] ∧ Effect4.Prim.arms
  (Effect4.Prim.async register withSignal cancel) = [])

#check (@Effect4.Prim.ofExit_asExit? :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.asExit? (Effect4.Prim.ofExit exit) = Option.some exit)

#check (@Effect4.Prim.asExit?_success :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (value : β), Effect4.Prim.asExit?
  (Effect4.Prim.success value) = Option.some (Effect4.Exit.success value))

#check (@Effect4.Prim.asExit?_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (cause : Effect4.Cause ε δ ι α),
  Effect4.Prim.asExit? (Effect4.Prim.failure cause) = Option.some (Effect4.Exit.failure cause))

#check (@Effect4.Prim.asExit?_eq_some :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α) (exit :
  Effect4.Exit β ε δ ι α), Effect4.Prim.asExit? self = Option.some exit → self =
  Effect4.Prim.ofExit exit)

#check (@Effect4.Prim.ofExit_isFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.isFrame (Effect4.Prim.ofExit exit) = Bool.false)

#check (@Effect4.Prim.ensure_of_no_contAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.false
  → Effect4.Prim.ensure frame fiber = (fiber, Option.none))

#check (@Effect4.Prim.ensure_onExit_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true →
  Effect4.Prim.ensure (Effect4.Prim.onExit body finalizer Bool.false) fiber =
  (Effect4.FrameFiber.mk fiber.current (Effect4.Prim.setInterruptible Bool.true :: fiber.stack)
  Bool.false fiber.interruptedCause fiber.deferredInterrupt, Option.none))

#check (@Effect4.Prim.ensure_onExit_told_not_to :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.ensure
  (Effect4.Prim.onExit body finalizer Bool.true) fiber = (fiber, Option.none))

#check (@Effect4.Prim.ensure_onExit_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible
  = Bool.false → Effect4.Prim.ensure (Effect4.Prim.onExit body finalizer flag) fiber = (fiber,
  Option.none))

#check (@Effect4.Prim.ensure_onExit_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), (Effect4.Prim.ensure
  (Effect4.Prim.onExit body finalizer flag) fiber).snd = Option.none)

#check (@Effect4.Prim.ensure_setInterruptible_flag :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.setInterruptible flag) fiber).fst.interruptible
  = flag)

#check (@Effect4.Prim.ensure_setInterruptible_stack :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.setInterruptible flag) fiber).fst.stack =
  fiber.stack)

#check (@Effect4.Prim.ensure_setInterruptible_substitutes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (cause : Effect4.Cause ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptedCause = Option.some cause →
  Effect4.Prim.ensure (Effect4.Prim.setInterruptible Bool.true) fiber = (Effect4.FrameFiber.mk
  fiber.current fiber.stack Bool.true fiber.interruptedCause fiber.deferredInterrupt,
  Option.some (Effect4.Prim.failure cause)))

#check (@Effect4.Prim.ensure_setInterruptible_false_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.Prim.ensure (Effect4.Prim.setInterruptible Bool.false) fiber).snd = Option.none)

#check (@Effect4.Prim.ensure_setInterruptible_no_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), fiber.interruptedCause = Option.none → Effect4.Prim.ensure
  (Effect4.Prim.setInterruptible flag) fiber = (Effect4.FrameFiber.mk fiber.current fiber.stack
  flag fiber.interruptedCause fiber.deferredInterrupt, Option.none))

#check (@Effect4.Prim.answerOf_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame next : Effect4.Prim ν σ β ε δ ι α)
  (demand : Effect4.Arm), Effect4.Prim.answerOf frame demand (Option.some next) = Option.some
  (Effect4.ContAnswer.replacement next))

#check (@Effect4.Prim.answerOf_arm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (demand
  : Effect4.Arm), Effect4.Prim.hasArm frame demand = Bool.true → Effect4.Prim.answerOf frame
  demand Option.none = Option.some (Effect4.ContAnswer.frame frame))

#check (@Effect4.Prim.answerOf_missing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (demand
  : Effect4.Arm), Effect4.Prim.hasArm frame demand = Bool.false → Effect4.Prim.answerOf frame
  demand Option.none = Option.none)

#check (@Effect4.Prim.answerOf_frame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame answering : Effect4.Prim ν σ β ε δ ι
  α) (demand : Effect4.Arm) (replacement : Option (Effect4.Prim ν σ β ε δ ι α)),
  Effect4.Prim.answerOf frame demand replacement = Option.some (Effect4.ContAnswer.frame
  answering) → answering = frame ∧ Effect4.Prim.hasArm frame demand = Bool.true)

#check (@Effect4.Prim.armA_isSome :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (frame : Effect4.Prim ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε δ ι
  α)), Option.isSome (Effect4.Prim.armA interp frame value provided) = Effect4.Prim.hasArm frame
  Effect4.Arm.contA)

#check (@Effect4.Prim.armE_isSome :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (frame : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), Option.isSome (Effect4.Prim.armE interp frame cause provided) =
  Effect4.Prim.hasArm frame Effect4.Arm.contE)

#check (@Effect4.Prim.armA_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onSuccess body onValue)
  value provided = Option.some (interp.contA onValue value, []))

#check (@Effect4.Prim.armA_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onSuccessAndFailure body
  onValue onCause) value provided = Option.some (interp.contA onValue value, []))

#check (@Effect4.Prim.armE_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause : ν) (cause : Effect4.Cause ε δ ι α) (provided
  : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.onFailure body
  onCause) cause provided = Option.some (interp.contE onCause cause, []))

#check (@Effect4.Prim.armE_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (cause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) cause provided = Option.some
  (interp.contE onCause cause, []))

#check (@Effect4.Prim.armE_onSuccess_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue : ν) (cause : Effect4.Cause ε δ ι α) (provided
  : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.onSuccess body
  onValue) cause provided = Option.none)

#check (@Effect4.Prim.armA_onFailure_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onFailure body onCause)
  value provided = Option.none)

#check (@Effect4.Prim.armA_setInterruptible_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (flag : Bool) (value : β) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA
  interp (Effect4.Prim.setInterruptible flag) value provided = Option.none)

#check (@Effect4.Prim.armE_setInterruptible_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (flag : Bool) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι α)),
  Effect4.Prim.armE interp (Effect4.Prim.setInterruptible flag) cause provided = Option.none)

#check (@Effect4.Prim.armE_whileLoop_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor : β) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β
  ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.whileLoop loop cursor) cause provided =
  Option.none)

#check (@Effect4.Prim.armE_iterator_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor : β) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.iterator generator cursor)
  cause provided = Option.none)

#check (@Effect4.Prim.armA_exitFrame_provided :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (value : β) (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.armA interp (Effect4.Prim.exitFrame body) value (Option.some exit) = Option.some
  (Effect4.Prim.success (interp.reifyExit exit), []))

#check (@Effect4.Prim.armA_exitFrame_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (value : β), Effect4.Prim.armA interp
  (Effect4.Prim.exitFrame body) value Option.none = Option.some (Effect4.Prim.success
  (interp.reifyExit (Effect4.Exit.success value)), []))

#check (@Effect4.Prim.armE_exitFrame_provided :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (exit : Effect4.Exit β
  ε δ ι α), Effect4.Prim.armE interp (Effect4.Prim.exitFrame body) cause (Option.some exit) =
  Option.some (Effect4.Prim.success (interp.reifyExit exit), []))

#check (@Effect4.Prim.armE_exitFrame_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α), Effect4.Prim.armE
  interp (Effect4.Prim.exitFrame body) cause Option.none = Option.some (Effect4.Prim.success
  (interp.reifyExit (Effect4.Exit.failure cause)), []))

#check (@Effect4.Prim.armA_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value : β) (exit :
  Effect4.Exit β ε δ ι α), Effect4.Prim.armA interp (Effect4.Prim.onExit body finalizer flag)
  value (Option.some exit) = Option.some (Effect4.Prim.ofExit
  (Effect4.Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)), []))

#check (@Effect4.Prim.armE_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (cause : Effect4.Cause ε
  δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.armE interp (Effect4.Prim.onExit body
  finalizer flag) cause (Option.some exit) = Option.some (Effect4.Prim.ofExit
  (Effect4.Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)), []))

#check (@Effect4.Prim.onExit_finalizer_success_restores :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value : β) (exit :
  Effect4.Exit β ε δ ι α), interp.finalizerExit finalizer exit = Effect4.Exit.success () →
  Effect4.Prim.armA interp (Effect4.Prim.onExit body finalizer flag) value (Option.some exit) =
  Option.some (Effect4.Prim.ofExit exit, []))

#check (@Effect4.Prim.onExit_finalizer_failure_merges :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (cause finalizerCause :
  Effect4.Cause ε δ ι α), interp.finalizerExit finalizer (Effect4.Exit.failure cause) =
  Effect4.Exit.failure finalizerCause → Effect4.Prim.armE interp (Effect4.Prim.onExit body
  finalizer flag) cause (Option.some (Effect4.Exit.failure cause)) = Option.some
  (Effect4.Prim.failure (Effect4.Cause.combine cause finalizerCause), []))

#check (@Effect4.Prim.onExit_success_finalizer_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value produced : β)
  (finalizerCause : Effect4.Cause ε δ ι α), interp.finalizerExit finalizer (Effect4.Exit.success
  produced) = Effect4.Exit.failure finalizerCause → Effect4.Prim.armA interp
  (Effect4.Prim.onExit body finalizer flag) value (Option.some (Effect4.Exit.success produced))
  = Option.some (Effect4.Prim.failure finalizerCause, []))

#check (@Effect4.Prim.onExit_arm_is_per_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body other : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag otherFlag : Bool) (value :
  β) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onExit
  body finalizer flag) value provided = Effect4.Prim.armA interp (Effect4.Prim.onExit other
  finalizer otherFlag) value provided)

#check (@Effect4.Prim.onSuccess_arm_is_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (left right : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), interp.contA left value ≠ interp.contA right value →
  Effect4.Prim.armA interp (Effect4.Prim.onSuccess body left) value provided ≠ Effect4.Prim.armA
  interp (Effect4.Prim.onSuccess body right) value provided)

#check (@Effect4.Prim.onFailure_arm_is_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (left right : ν) (cause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), interp.contE left cause ≠ interp.contE right
  cause → Effect4.Prim.armE interp (Effect4.Prim.onFailure body left) cause provided ≠
  Effect4.Prim.armE interp (Effect4.Prim.onFailure body right) cause provided)

#check (@Effect4.Prim.onSuccessAndFailure_arms_are_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (cause :
  Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) value provided = Option.some
  (interp.contA onValue value, []) ∧ Effect4.Prim.armE interp (Effect4.Prim.onSuccessAndFailure
  body onValue onCause) cause provided = Option.some (interp.contE onCause cause, []))

#check (@Effect4.Prim.armA_whileLoop_continue :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)), interp.loopTest
  loop (interp.loopStep loop value) = Bool.true → Effect4.Prim.armA interp
  (Effect4.Prim.whileLoop loop cursor) value provided = Option.some (interp.loopBody loop
  (interp.loopStep loop value), [Effect4.Prim.whileLoop loop (interp.loopStep loop value)]))

#check (@Effect4.Prim.armA_whileLoop_stop :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)), interp.loopTest
  loop (interp.loopStep loop value) = Bool.false → Effect4.Prim.armA interp
  (Effect4.Prim.whileLoop loop cursor) value provided = Option.some (Effect4.Prim.success
  (interp.loopDone loop), []))

#check (@Effect4.Prim.armA_iterator_done :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value result : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  (interp.iterNext generator value).snd = Effect4.IterStep.done result → Effect4.Prim.armA
  interp (Effect4.Prim.iterator generator cursor) value provided = Option.some
  (Effect4.Prim.success result, []))

#check (@Effect4.Prim.armA_iterator_halt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value : β) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), (interp.iterNext generator value).snd = Effect4.IterStep.halt cause
  → Effect4.Prim.armA interp (Effect4.Prim.iterator generator cursor) value provided =
  Option.some (Effect4.Prim.failure cause, []))

#check (@Effect4.Prim.armA_iterator_resume :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value : β) (next : Effect4.Prim ν σ β ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), (interp.iterNext generator value).snd = Effect4.IterStep.resume
  next → Effect4.Prim.armA interp (Effect4.Prim.iterator generator cursor) value provided =
  Option.some (next, [Effect4.Prim.iterator generator cursor]))

#check (@Effect4.Prim.iteratorFolded_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value :
  β), Effect4.Prim.iteratorFolded interp (Effect4.Prim.iterator generator cursor) value =
  (interp.iterNext generator value).fst)

#check (@Effect4.Prim.iterator_folds_inline :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (left right : Effect4.PrimInterp ν σ β ε
  δ ι α) (generator : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  (left.iterNext generator value).snd = (right.iterNext generator value).snd → Effect4.Prim.armA
  left (Effect4.Prim.iterator generator cursor) value provided = Effect4.Prim.armA right
  (Effect4.Prim.iterator generator cursor) value provided)

#check (@Effect4.Prim.finalizerEvents_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents
  (Effect4.Prim.onExit body finalizer flag) exit = [Effect4.FrameEvent.ranFinalizer finalizer
  exit])

#check (@Effect4.Prim.finalizerEvents_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  : ν) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents (Effect4.Prim.onSuccess
  body onValue) exit = [])

#check (@Effect4.Prim.finalizerEvents_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onCause
  : ν) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents (Effect4.Prim.onFailure
  body onCause) exit = [])

#check (@Effect4.FrameFiber.getCont_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.true → Effect4.FrameFiber.getCont self
  demand Bool.false = Effect4.FramePop.mk (Effect4.ContAnswer.deferred
  (Effect4.FrameFiber.pendingCause self)) [] [Effect4.FrameEvent.deferred
  (Effect4.FrameFiber.pendingCause self)] (Effect4.FrameFiber.mk self.current self.stack
  self.interruptible self.interruptedCause Bool.false))

#check (@Effect4.FrameFiber.getCont_deferred_pops_nothing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.true → (Effect4.FrameFiber.getCont self
  demand Bool.false).popped = [])

#check (@Effect4.FrameFiber.getCont_eq_popFrom :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.deferredInterrupt = Bool.false →
  Effect4.FrameFiber.getCont self demand skip = Effect4.FrameFiber.popFrom demand skip
  self.stack (Effect4.FrameFiber.mk self.current [] self.interruptible self.interruptedCause
  Bool.false))

#check (@Effect4.FrameFiber.getCont_skip_clears_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), Effect4.FrameFiber.getCont self demand Bool.true =
  Effect4.FrameFiber.popFrom demand Bool.true self.stack (Effect4.FrameFiber.mk self.current []
  self.interruptible self.interruptedCause Bool.false))

#check (@Effect4.FrameFiber.getCont_empty_stack :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.deferredInterrupt = Bool.false → self.stack = [] →
  Effect4.FrameFiber.getCont self demand skip = Effect4.FramePop.mk Effect4.ContAnswer.empty []
  [] (Effect4.FrameFiber.mk self.current [] self.interruptible self.interruptedCause
  Bool.false))

#check (@Effect4.FrameFiber.popFrom_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.FrameFiber.popFrom demand skip [] fiber =
  Effect4.FramePop.mk Effect4.ContAnswer.empty [] [] fiber)

#check (@Effect4.FrameFiber.popFrom_answer_answer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).answer = answer)

#check (@Effect4.FrameFiber.popFrom_answer_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).popped = [frame])

#check (@Effect4.FrameFiber.popFrom_answer_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).events =
  Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd)

#check (@Effect4.FrameFiber.popFrom_answer_fiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).fiber = have __src :=
  (Effect4.Prim.ensure frame fiber).fst; Effect4.FrameFiber.mk __src.current
  ((Effect4.Prim.ensure frame fiber).fst.stack ++ rest) __src.interruptible
  __src.interruptedCause __src.deferredInterrupt)

#check (@Effect4.FrameFiber.popFrom_continue_answer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).answer = (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).answer)

#check (@Effect4.FrameFiber.popFrom_continue_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).popped = frame :: (Effect4.FrameFiber.continueFrom demand skip frame rest
  fiber).popped)

#check (@Effect4.FrameFiber.popFrom_continue_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).events = Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd ++
  (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).events)

#check (@Effect4.FrameFiber.popFrom_continue_fiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).fiber = (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).fiber)

#check (@Effect4.FrameFiber.popFrom_answer_hasArm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (frame :
  Effect4.Prim ν σ β ε δ ι α), (Effect4.FrameFiber.popFrom demand skip frames fiber).answer =
  Effect4.ContAnswer.frame frame → Effect4.Prim.hasArm frame demand = Bool.true)

#check (@Effect4.FrameFiber.getCont_answer_hasArm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (frame : Effect4.Prim ν σ β ε δ ι α),
  (Effect4.FrameFiber.getCont self demand skip).answer = Effect4.ContAnswer.frame frame →
  Effect4.Prim.hasArm frame demand = Bool.true)

#check (@Effect4.FrameFiber.passEvents_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α)
  (replacement : Option (Effect4.Prim ν σ β ε δ ι α)), Effect4.Prim.hasArm frame
  Effect4.Arm.contAll = Bool.true → Effect4.FrameEvent.ranContAll frame ∈
  Effect4.Prim.passEvents frame replacement)

#check (@Effect4.FrameFiber.passEvents_poppedFrames :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α)
  (replacement : Option (Effect4.Prim ν σ β ε δ ι α)), Effect4.FrameEvent.poppedFrames
  (Effect4.Prim.passEvents frame replacement) = [frame])

#check (@Effect4.FrameFiber.popFrom_popped_eq_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.popFrom demand skip frames fiber).popped = Effect4.FrameEvent.poppedFrames
  (Effect4.FrameFiber.popFrom demand skip frames fiber).events)

#check (@Effect4.FrameFiber.popFrom_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (frame :
  Effect4.Prim ν σ β ε δ ι α), Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.true → frame
  ∈ (Effect4.FrameFiber.popFrom demand skip frames fiber).popped → Effect4.FrameEvent.ranContAll
  frame ∈ (Effect4.FrameFiber.popFrom demand skip frames fiber).events)

#check (@Effect4.FrameFiber.getCont_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (frame : Effect4.Prim ν σ β ε δ ι α),
  self.deferredInterrupt = Bool.false → Effect4.Prim.hasArm frame Effect4.Arm.contAll =
  Bool.true → frame ∈ (Effect4.FrameFiber.getCont self demand skip).popped →
  Effect4.FrameEvent.ranContAll frame ∈ (Effect4.FrameFiber.getCont self demand skip).events)

#check (@Effect4.FrameFiber.getCont_skip_of_no_pending_cause :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.false → self.interruptedCause =
  Option.none → Effect4.FrameFiber.getCont self demand Bool.true = Effect4.FrameFiber.getCont
  self demand Bool.false)

#check (@Effect4.FrameFiber.interrupt_skips_every_handler :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (cause : Effect4.Cause ε δ ι α), self.interruptible = Bool.true →
  self.interruptedCause = Option.some cause → (∀ (frame : Effect4.Prim ν σ β ε δ ι α), frame ∈
  self.stack → Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.false) →
  (Effect4.FrameFiber.getCont self demand Bool.true).answer = Effect4.ContAnswer.empty)

#check (@Effect4.FrameFiber.getCont_mask_stops_skip :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (skip : Bool) (rest : List (Effect4.Prim ν σ β ε δ ι α)), self.deferredInterrupt = Bool.false
  → self.stack = Effect4.Prim.setInterruptible Bool.false :: rest → (Effect4.FrameFiber.getCont
  self Effect4.Arm.contE skip).answer = (Effect4.FrameFiber.getCont (Effect4.FrameFiber.mk
  self.current rest Bool.false self.interruptedCause Bool.false) Effect4.Arm.contE skip).answer)

#check (@Effect4.FrameFiber.resumeValue_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).answer =
  Effect4.ContAnswer.empty → Effect4.FrameFiber.resumeValue interp self value provided =
  (Effect4.FrameStep.finished (Option.getD provided (Effect4.Exit.success value)),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).events ++
  [Effect4.FrameEvent.yielded (Option.getD provided (Effect4.Exit.success value))]))

#check (@Effect4.FrameFiber.resumeValue_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (cause : Effect4.Cause ε δ ι α), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).answer = Effect4.ContAnswer.deferred cause → Effect4.FrameFiber.resumeValue interp
  self value provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont
  self Effect4.Arm.contA Bool.false).fiber; Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
  __src.stack __src.interruptible __src.interruptedCause __src.deferredInterrupt),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).events))

#check (@Effect4.FrameFiber.resumeValue_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (next : Effect4.Prim ν σ β ε δ ι α), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contA Bool.false).answer = Effect4.ContAnswer.replacement next →
  Effect4.FrameFiber.resumeValue interp self value provided = (Effect4.FrameStep.running (have
  __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).fiber;
  Effect4.FrameFiber.mk next __src.stack __src.interruptible __src.interruptedCause
  __src.deferredInterrupt), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).events))

#check (@Effect4.FrameFiber.resumeValue_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (frame next : Effect4.Prim ν σ β ε δ ι α) (pushed : List (Effect4.Prim ν σ β ε δ ι
  α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).answer =
  Effect4.ContAnswer.frame frame → Effect4.Prim.armA interp frame value provided = Option.some
  (next, pushed) → Effect4.FrameFiber.resumeValue interp self value provided =
  (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).fiber; Effect4.FrameFiber.mk next (pushed ++ (Effect4.FrameFiber.getCont self
  Effect4.Arm.contA Bool.false).fiber.stack) __src.interruptible __src.interruptedCause
  __src.deferredInterrupt), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).events ++ Effect4.Prim.finalizerEvents frame (Option.getD provided
  (Effect4.Exit.success value)) ++ List.map Effect4.FrameEvent.pushed pushed))

#check (@Effect4.FrameFiber.resumeCause_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE
  Bool.true).answer = Effect4.ContAnswer.empty → Effect4.FrameFiber.resumeCause interp self
  cause provided = (Effect4.FrameStep.finished (Option.getD provided (Effect4.Exit.failure
  cause)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).events ++
  [Effect4.FrameEvent.yielded (Option.getD provided (Effect4.Exit.failure cause))]))

#check (@Effect4.FrameFiber.resumeCause_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause deferredCause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).answer = Effect4.ContAnswer.deferred deferredCause →
  Effect4.FrameFiber.resumeCause interp self cause provided = (Effect4.FrameStep.running (have
  __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).fiber;
  Effect4.FrameFiber.mk (Effect4.Prim.failure deferredCause) __src.stack __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events))

#check (@Effect4.FrameFiber.resumeCause_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)) (next : Effect4.Prim ν σ β ε δ ι α),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).answer =
  Effect4.ContAnswer.replacement next → Effect4.FrameFiber.resumeCause interp self cause
  provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).fiber; Effect4.FrameFiber.mk next __src.stack __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events))

#check (@Effect4.FrameFiber.resumeCause_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)) (frame next : Effect4.Prim ν σ β ε δ ι α) (pushed : List
  (Effect4.Prim ν σ β ε δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE
  Bool.true).answer = Effect4.ContAnswer.frame frame → Effect4.Prim.armE interp frame cause
  provided = Option.some (next, pushed) → Effect4.FrameFiber.resumeCause interp self cause
  provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).fiber; Effect4.FrameFiber.mk next (pushed ++
  (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).fiber.stack) __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events ++ Effect4.Prim.finalizerEvents frame (Option.getD
  provided (Effect4.Exit.failure cause)) ++ List.map Effect4.FrameEvent.pushed pushed))

#check (@Effect4.FrameFiber.step_success :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.success value) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = Effect4.FrameFiber.resumeValue interp
  (Effect4.FrameFiber.mk (Effect4.Prim.success value) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) value (Option.some (Effect4.Exit.success
  value)))

#check (@Effect4.FrameFiber.step_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α),
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt) =
  Effect4.FrameFiber.resumeCause interp (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt) cause (Option.some
  (Effect4.Exit.failure cause)))

#check (@Effect4.FrameFiber.step_sync :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.sync thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = Effect4.FrameFiber.resumeValue interp
  (Effect4.FrameFiber.mk (Effect4.Prim.sync thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) (interp.syncValue thunk) Option.none)

#check (@Effect4.FrameFiber.step_suspend :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.suspend thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_withFiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.withFiber thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_yieldableError :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (error : ε), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.yieldableError error) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.fail error)) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onSuccess body
  onValue) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onSuccess body onValue ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccess body onValue)]))

#check (@Effect4.FrameFiber.step_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onFailure body
  onCause) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onFailure body onCause ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onFailure body onCause)]))

#check (@Effect4.FrameFiber.step_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  onCause : ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk body (Effect4.Prim.onSuccessAndFailure body onValue onCause ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccessAndFailure body onValue onCause)]))

#check (@Effect4.FrameFiber.step_exitFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α),
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.exitFrame body) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk body (Effect4.Prim.exitFrame body :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed
  (Effect4.Prim.exitFrame body)]))

#check (@Effect4.FrameFiber.step_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer :
  ν) (flag : Bool), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onExit
  body finalizer flag) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk body
  (Effect4.Prim.onExit body finalizer flag :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed (Effect4.Prim.onExit
  body finalizer flag)]))

#check (@Effect4.FrameFiber.step_setInterruptible_not_evaluable :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (flag : Bool), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.setInterruptible flag) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.die interp.notImplemented))
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_whileLoop_true :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (loop : ν) (cursor : β), interp.loopTest loop
  cursor = Bool.true → Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.whileLoop loop cursor) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk (interp.loopBody
  loop cursor) (Effect4.Prim.whileLoop loop cursor :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed
  (Effect4.Prim.whileLoop loop cursor)]))

#check (@Effect4.FrameFiber.step_whileLoop_false :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (loop : ν) (cursor : β), interp.loopTest loop
  cursor = Bool.false → Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.whileLoop loop cursor) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk
  (Effect4.Prim.success (interp.loopDone loop)) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_iterator :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (generator : ν) (cursor : β) (next : Effect4.Prim
  ν σ β ε δ ι α) (pushed : List (Effect4.Prim ν σ β ε δ ι α)), Effect4.Prim.armA interp
  (Effect4.Prim.iterator generator cursor) cursor Option.none = Option.some (next, pushed) →
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.iterator generator cursor)
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk next (pushed ++ self.stack)
  self.interruptible self.interruptedCause self.deferredInterrupt), List.map
  Effect4.FrameEvent.pushed pushed))

#check (@Effect4.FrameFiber.step_ofExit_finishes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (exit : Effect4.Exit β ε δ ι α), Effect4.FrameFiber.step interp (Effect4.FrameFiber.start
  (Effect4.Prim.ofExit exit)) = (Effect4.FrameStep.finished exit, [Effect4.FrameEvent.yielded
  exit]))

#check (@Effect4.FrameFiber.run_zero :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α), Effect4.FrameFiber.run interp 0 self =
  (Effect4.FrameStep.running self, []))

#check (@Effect4.FrameFiber.run_succ_finished :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (fuel : Nat) (exit : Effect4.Exit β ε δ ι α)
  (events : List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameFiber.step interp self =
  (Effect4.FrameStep.finished exit, events) → Effect4.FrameFiber.run interp (fuel + 1) self =
  (Effect4.FrameStep.finished exit, events))

#check (@Effect4.FrameFiber.run_succ_running :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self next : Effect4.FrameFiber ν σ β ε δ ι α) (fuel : Nat) (events : List
  (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameFiber.step interp self =
  (Effect4.FrameStep.running next, events) → Effect4.FrameFiber.run interp (fuel + 1) self =
  ((Effect4.FrameFiber.run interp fuel next).fst, events ++ (Effect4.FrameFiber.run interp fuel
  next).snd))

#check (@Effect4.FrameFiber.uninterruptible_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.false → Effect4.FrameFiber.uninterruptible self = self)

#check (@Effect4.FrameFiber.uninterruptible_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.true → Effect4.FrameFiber.uninterruptible self =
  Effect4.FrameFiber.mk self.current (Effect4.Prim.setInterruptible Bool.true :: self.stack)
  Bool.false self.interruptedCause self.deferredInterrupt)

#check (@Effect4.FrameFiber.uninterruptibleMask_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.uninterruptibleMask self = Effect4.FrameFiber.uninterruptible self)

#check (@Effect4.FrameFiber.setFiberInterruptible_flag :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.setFiberInterruptible self).fst.interruptible = Bool.true)

#check (@Effect4.FrameFiber.setFiberInterruptible_pushes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.setFiberInterruptible self).fst.stack = Effect4.Prim.setInterruptible
  Bool.false :: self.stack)

#check (@Effect4.FrameFiber.setFiberInterruptible_immediate_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (cause : Effect4.Cause ε δ ι α), self.interruptedCause = Option.some cause →
  (Effect4.FrameFiber.setFiberInterruptible self).snd = Option.some (Effect4.Prim.failure
  cause))

#check (@Effect4.FrameFiber.setFiberInterruptible_no_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptedCause = Option.none → (Effect4.FrameFiber.setFiberInterruptible self).snd =
  Option.none)

#check (@Effect4.FrameFiber.interruptibleRegion_already :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.true → Effect4.FrameFiber.interruptibleRegion self = (self,
  Option.none))

#check (@Effect4.FrameFiber.interruptibleRegion_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.false → Effect4.FrameFiber.interruptibleRegion self =
  Effect4.FrameFiber.setFiberInterruptible self)

#check (@Effect4.FrameFiber.restoreAcquire_asked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.restoreAcquire self Bool.true = Effect4.FrameFiber.interruptibleRegion
  self)

#check (@Effect4.FrameFiber.restoreAcquire_not_asked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.restoreAcquire self Bool.false = (self, Option.none))

#check (@Effect4.Prim.scopedFrame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (body : Effect4.Prim ν σ β ε δ ι α) (closeScope : ν),
  Effect4.Prim.scopedFrame body closeScope = Effect4.Prim.onExit body closeScope Bool.false)

#check (@Effect4.Prim.scopedFrame_finalizer_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (body : Effect4.Prim ν σ β ε δ ι α) (closeScope : ν) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true → Effect4.Prim.ensure
  (Effect4.Prim.scopedFrame body closeScope) fiber = (Effect4.FrameFiber.mk fiber.current
  (Effect4.Prim.setInterruptible Bool.true :: fiber.stack) Bool.false fiber.interruptedCause
  fiber.deferredInterrupt, Option.none))

#check (@Effect4.FrameFiber.step_scopedFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (closeScope :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.scopedFrame body
  closeScope) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onExit body closeScope
  Bool.false :: self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onExit body closeScope Bool.false)]))

#check (@Effect4.Prim.withFiber_refused :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] {ϑ : Type u} (resolve : Effect4.FrameFiber ν σ β ε δ ι α → ϑ) (left right :
  Effect4.FrameFiber ν σ β ε δ ι α), left = right → resolve left = resolve right)

#check (@Effect4.Prim.yieldableError_host_class_refused :
  ∀ {ε : Type u} [DecidableEq ε] {ϑ : Type u} (host : ε → ϑ) (left right : ε), left = right →
  host left = host right)

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
  , "exit", "cause", "entry", "rule", "ref", "deferred", "layer" ]

private def knownCoverage : List String := ["green", "partial", "absent"]

private def censusRows : List Row :=
  [ { id := "op.Success", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.getCont_empty_stack "propext"
        , w `Effect4.FrameFiber.resumeValue_empty "propext"
        , w `Effect4.FrameFiber.resumeValue_frame "propext"
        , w `Effect4.FrameFiber.step_success "propext"
        , w `Effect4.FrameFiber.step_ofExit_finishes "propext" ] }
  , { id := "op.Failure", kind := "op", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "annotates the cause with the current stack frame" needs a fiber Context and a StackTrace service key
    , witnesses :=
        [ w `Effect4.FrameFiber.interrupt_skips_every_handler "propext,Quot.sound"
        , w `Effect4.FrameFiber.resumeCause_empty "propext"
        , w `Effect4.FrameFiber.resumeCause_frame "propext"
        , w `Effect4.FrameFiber.step_failure "propext" ] }
  , { id := "op.WithFiber", kind := "op", disposition := "foreignBoundary", coverage := "green"
      -- the raw FiberImpl host-identity clause is closed by refusal, not by a model
    , witnesses :=
        [ w `Effect4.FrameFiber.step_withFiber "propext"
        , w `Effect4.Prim.withFiber_refused "none" ] }
  , { id := "op.YieldableError", kind := "op", disposition := "foreignBoundary", coverage := "green"
      -- the host Error subclass identity clause is closed by refusal, not by a model
    , witnesses :=
        [ w `Effect4.FrameFiber.step_yieldableError "propext"
        , w `Effect4.Prim.yieldableError_host_class_refused "none" ] }
  , { id := "op.Sync", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.step_sync "propext" ] }
  , { id := "op.Suspend", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.step_suspend "propext" ] }
  , { id := "op.Yield", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.Async", kind := "op", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "op.AsyncFinalizer", kind := "op", disposition := "excludedInternal", coverage := "absent", witnesses := [] }
  , { id := "op.Iterator", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_iterator_done "propext"
        , w `Effect4.Prim.armA_iterator_halt "propext"
        , w `Effect4.Prim.armA_iterator_resume "propext"
        , w `Effect4.Prim.iteratorFolded_eq "none"
        , w `Effect4.Prim.iterator_folds_inline "propext"
        , w `Effect4.FrameFiber.step_iterator "propext" ] }
  , { id := "op.OnSuccess", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_onSuccess "none"
        , w `Effect4.Prim.onSuccess_arm_is_per_instance "none"
        , w `Effect4.FrameFiber.step_onSuccess "propext" ] }
  , { id := "op.OnFailure", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armE_onFailure "none"
        , w `Effect4.Prim.onFailure_arm_is_per_instance "none"
        , w `Effect4.FrameFiber.step_onFailure "propext" ] }
  , { id := "op.OnSuccessAndFailure", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_onSuccessAndFailure "none"
        , w `Effect4.Prim.armE_onSuccessAndFailure "none"
        , w `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance "none"
        , w `Effect4.FrameFiber.step_onSuccessAndFailure "propext" ] }
  , { id := "op.Exit", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_exitFrame_provided "none"
        , w `Effect4.Prim.armA_exitFrame_none "none"
        , w `Effect4.Prim.armE_exitFrame_provided "none"
        , w `Effect4.Prim.armE_exitFrame_none "none"
        , w `Effect4.FrameFiber.step_exitFrame "propext" ] }
  , { id := "op.OnExit", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.ensure_onExit_masks "propext"
        , w `Effect4.Prim.ensure_onExit_told_not_to "propext"
        , w `Effect4.Prim.ensure_onExit_already_masked "propext"
        , w `Effect4.Prim.armA_onExit "none"
        , w `Effect4.Prim.armE_onExit "none"
        , w `Effect4.Prim.onExit_finalizer_success_restores "none"
        , w `Effect4.Prim.onExit_finalizer_failure_merges "none"
        , w `Effect4.Prim.onExit_success_finalizer_failure "none"
        , w `Effect4.Prim.finalizerEvents_onExit "none"
        , w `Effect4.Prim.finalizerEvents_onSuccess "none"
        , w `Effect4.Prim.finalizerEvents_onFailure "none"
        , w `Effect4.FrameFiber.step_onExit "propext" ] }
  , { id := "op.SetInterruptible", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_setInterruptible "none"
        , w `Effect4.Prim.ensure_setInterruptible_flag "propext"
        , w `Effect4.Prim.ensure_setInterruptible_stack "propext"
        , w `Effect4.Prim.ensure_setInterruptible_substitutes "propext"
        , w `Effect4.Prim.ensure_setInterruptible_false_no_replacement "propext"
        , w `Effect4.Prim.ensure_setInterruptible_no_pending "propext"
        , w `Effect4.Prim.armA_setInterruptible_none "none"
        , w `Effect4.Prim.armE_setInterruptible_none "none"
        , w `Effect4.FrameFiber.step_setInterruptible_not_evaluable "propext" ] }
  , { id := "op.While", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_whileLoop_continue "propext"
        , w `Effect4.Prim.armA_whileLoop_stop "propext"
        , w `Effect4.FrameFiber.step_whileLoop_true "propext"
        , w `Effect4.FrameFiber.step_whileLoop_false "propext" ] }
  , { id := "frame-arm.OnSuccess", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onSuccess "none"
        , w `Effect4.Prim.armA_isSome "propext"
        , w `Effect4.Prim.armE_isSome "none"
        , w `Effect4.Prim.armE_onSuccess_none "none"
        , w `Effect4.Prim.onSuccess_arm_is_per_instance "none" ] }
  , { id := "frame-arm.OnFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onFailure "none"
        , w `Effect4.Prim.armA_onFailure_none "none"
        , w `Effect4.Prim.onFailure_arm_is_per_instance "none" ] }
  , { id := "frame-arm.OnSuccessAndFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onSuccessAndFailure "none"
        , w `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance "none" ] }
  , { id := "frame-arm.Exit", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_exitFrame "none"
        , w `Effect4.Prim.ensure_of_no_contAll "none" ] }
  , { id := "frame-arm.OnExit", kind := "frame-arm", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.cleanup_preserves_terminal "propext"
        , w `Effect4.cleanup_at_most_once "propext,Quot.sound"
        , w `Effect4.cleanup_events_at_most_once "propext,Quot.sound"
        , w `Effect4.cleanup_count_monotone "propext,Quot.sound"
        , w `Effect4.cleanup_safe_on_finish "propext,Quot.sound"
        , w `Effect4.Prim.arms_onExit "none"
        , w `Effect4.Prim.ensure_onExit_masks "propext"
        , w `Effect4.Prim.ensure_onExit_told_not_to "propext"
        , w `Effect4.Prim.ensure_onExit_already_masked "propext"
        , w `Effect4.Prim.ensure_onExit_no_replacement "propext"
        , w `Effect4.Prim.onExit_arm_is_per_frame "none" ] }
  , { id := "frame-arm.SetInterruptible", kind := "frame-arm", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.enter_mask_exists "propext"
        , w `Effect4.Prim.arms_setInterruptible "none"
        , w `Effect4.Prim.ensure_setInterruptible_substitutes "propext"
        , w `Effect4.Prim.answerOf_replacement "none"
        , w `Effect4.Prim.armA_setInterruptible_none "none"
        , w `Effect4.Prim.armE_setInterruptible_none "none"
        , w `Effect4.FrameFiber.resumeValue_replacement "propext"
        , w `Effect4.FrameFiber.resumeCause_replacement "propext" ] }
  , { id := "frame-arm.AsyncFinalizer", kind := "frame-arm", disposition := "excludedInternal", coverage := "absent", witnesses := [] }
  , { id := "frame-arm.While", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_whileLoop "none"
        , w `Effect4.Prim.armE_whileLoop_none "none"
        , w `Effect4.FrameFiber.step_whileLoop_true "propext" ] }
  , { id := "frame-arm.Iterator", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_iterator "none"
        , w `Effect4.Prim.armE_iterator_none "none"
        , w `Effect4.FrameFiber.step_iterator "propext" ] }
  , { id := "checkpoint.runloop-top", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.getcont-deferred", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.pendingCause_some "none"
        , w `Effect4.FrameFiber.pendingCause_none "none"
        , w `Effect4.FrameFiber.getCont_deferred "propext"
        , w `Effect4.FrameFiber.getCont_deferred_pops_nothing "propext"
        , w `Effect4.FrameFiber.getCont_skip_clears_deferred "propext"
        , w `Effect4.FrameFiber.resumeValue_deferred "propext"
        , w `Effect4.FrameFiber.resumeCause_deferred "propext" ] }
  , { id := "checkpoint.post-yield-cancel", kind := "checkpoint", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "checkpoint.exit-failcause-skip", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.popFrom_continue_answer "propext"
        , w `Effect4.FrameFiber.getCont_skip_of_no_pending_cause "propext,Quot.sound"
        , w `Effect4.FrameFiber.interrupt_skips_every_handler "propext,Quot.sound" ] }
  , { id := "checkpoint.set-fiber-interruptible", kind := "checkpoint", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.pending_unmask_exists "propext"
        , w `Effect4.unmask_without_pending_exists "propext"
        , w `Effect4.FrameFiber.setFiberInterruptible_flag "none"
        , w `Effect4.FrameFiber.setFiberInterruptible_pushes "none"
        , w `Effect4.FrameFiber.setFiberInterruptible_immediate_failure "propext"
        , w `Effect4.FrameFiber.setFiberInterruptible_no_pending "propext"
        , w `Effect4.FrameFiber.interruptibleRegion_already "propext"
        , w `Effect4.FrameFiber.interruptibleRegion_masked "propext" ] }
  , { id := "checkpoint.set-interruptible-contall", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.ensure_setInterruptible_substitutes "propext"
        , w `Effect4.Prim.answerOf_replacement "none"
        , w `Effect4.FrameFiber.resumeValue_replacement "propext"
        , w `Effect4.FrameFiber.resumeCause_replacement "propext" ] }
  , { id := "interrupt.unsafe-entry", kind := "interrupt", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.unmasked_interrupt_delivers "propext"
        , w `Effect4.unmasked_request_exists "propext"
        , w `Effect4.masked_request_exists "propext" ] }
  -- Remaining source clause: Actual FiberId/annotation interpretation and integration of the
  -- recording facet with delivery. See SUPERVISION-PG-RC112.
  , { id := "interrupt.accumulate", kind := "interrupt", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.interruptCause_eq "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.recordInterrupt_done "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.recordInterrupt_live "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.recordInterrupt_core "propext,Quot.sound" ] }
  , { id := "fork.unsafe", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.MaskMode.select_interruptible "none"
        , w `Effect4.Supervision.MaskMode.select_uninterruptible "none"
        , w `Effect4.Supervision.MaskMode.select_inherit "none"
        , w `Effect4.Supervision.MaskMode.cases_receipt "propext"
        , w `Effect4.Supervision.Globals.valid_iff "none"
        , w `Effect4.Supervision.Globals.ownsChildren_iff "none"
        , w `Effect4.Supervision.Fiber.valid_iff "none"
        , w `Effect4.Supervision.Fiber.valid?_iff "propext"
        , w `Effect4.Supervision.Fiber.toFiberState_eq "none"
        , w `Effect4.Supervision.initialFiber_eq "none"
        , w `Effect4.Supervision.initialFiber_valid "propext"
        , w `Effect4.Supervision.commitFork_eq "propext"
        , w `Effect4.Supervision.forkUnsafe_duplicate "propext"
        , w `Effect4.Supervision.forkUnsafe_deferred "propext"
        , w `Effect4.Supervision.forkUnsafe_wrong_deferred "propext"
        , w `Effect4.Supervision.forkUnsafe_wrong_immediate "propext"
        , w `Effect4.Supervision.forkUnsafe_wrong_identity "propext"
        , w `Effect4.Supervision.forkUnsafe_wrong_parent "propext"
        , w `Effect4.Supervision.forkUnsafe_invalid_child "propext"
        , w `Effect4.Supervision.forkUnsafe_invalid_parent "propext"
        , w `Effect4.Supervision.forkUnsafe_invalid_globals "propext"
        , w `Effect4.Supervision.forkUnsafe_invalid_ownership "propext"
        , w `Effect4.Supervision.forkUnsafe_invalid_child_ownership "propext,Quot.sound"
        , w `Effect4.Supervision.forkUnsafe_immediate "propext,Quot.sound"
        , w `Effect4.Supervision.forkUnsafe_fresh "propext"
        , w `Effect4.Supervision.forkUnsafe_allocated_nodup "propext,Quot.sound"
        , w `Effect4.Supervision.forkUnsafe_child_valid "propext"
        , w `Effect4.Supervision.commitFork_done_untracked "propext"
        , w `Effect4.Supervision.Globals.allocate_eq "none"
        , w `Effect4.Supervision.Globals.extends_iff "none"
        , w `Effect4.Supervision.Globals.extends?_iff "propext"
        , w `Effect4.Supervision.Globals.ownsChildren?_iff "propext,Quot.sound" ] }
  -- Remaining source clause: Installing the real global middleware; child completion invoking its
  -- parent observer. See SUPERVISION-PG-RC112.
  , { id := "fork.child", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.Globals.install_eq "none"
        , w `Effect4.Supervision.Fiber.removeChild_eq "none"
        , w `Effect4.Supervision.Fiber.addChild_nodup "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.removeChild_membership "propext,Quot.sound"
        , w `Effect4.Supervision.forkUnsafe_parent_children_nodup "propext,Quot.sound"
        , w `Effect4.Supervision.forkChild_eq "propext"
        , w `Effect4.Supervision.commitFork_done_untracked "propext"
        , w `Effect4.Supervision.Globals.extends_iff "none"
        , w `Effect4.Supervision.Globals.extends?_iff "propext"
        , w `Effect4.Supervision.Globals.ownsChildren?_iff "propext,Quot.sound"
        , w `Effect4.Supervision.beginParentExit_eq "none" ] }
  -- Remaining source clause: Actual daemon execution and independent lifetime. See SUPERVISION-PG-
  -- RC112.
  , { id := "fork.detach", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.forkDetach_eq "propext"
        , w `Effect4.Supervision.commitFork_daemon_untracked "propext" ] }
  -- Remaining source clause: Supplied post-start scope denotes the same mutable host scope;
  -- finalizer execution. See SUPERVISION-PG-RC112.
  , { id := "fork.in", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.ScopeMode.cases_receipt "propext"
        , w `Effect4.Supervision.bindScope_invalid "propext"
        , w `Effect4.Supervision.bindScope_done "propext"
        , w `Effect4.Supervision.bindScope_closed "propext"
        , w `Effect4.Supervision.bindScope_duplicate_key "propext"
        , w `Effect4.Supervision.bindScope_open "propext"
        , w `Effect4.Supervision.scopeFinalizerInterruptor_eq "none"
        , w `Effect4.Supervision.scopeFinalizer_self_guard "propext"
        , w `Effect4.Supervision.scopeObserver_eq "none"
        , w `Effect4.Supervision.scopeObserver_key_membership "propext,Quot.sound" ] }
  -- Remaining source clause: Ambient Scope service resolution and composition with fork startup.
  -- See SUPERVISION-PG-RC112.
  , { id := "fork.scoped", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.forkScopedBinding_eq "propext" ] }
  -- Remaining source clause: Actual first accepted callback resumption, request delivery, dynamic
  -- shared-set interpretation, uninterruptible continuation execution. See SUPERVISION-PG-RC112.
  , { id := "fork.race-all", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.WaitState.begin_eq "none"
        , w `Effect4.Supervision.WaitState.pending_eq "propext"
        , w `Effect4.Supervision.WaitState.ready_iff "propext"
        , w `Effect4.Supervision.WaitState.ready_publications "propext,Quot.sound"
        , w `Effect4.Supervision.WaitState.observe_pending "propext"
        , w `Effect4.Supervision.WaitState.observe_unknown "propext"
        , w `Effect4.Supervision.WaitState.observe_pending_membership "propext,Quot.sound"
        , w `Effect4.Supervision.waitStep_iff "propext"
        , w `Effect4.Supervision.waitRuns_iff "propext"
        , w `Effect4.Supervision.ReplayResult.state_done "none"
        , w `Effect4.Supervision.ReplayResult.state_frontier "none"
        , w `Effect4.Supervision.ReplayResult.state_refused "none"
        , w `Effect4.Supervision.waitReplay_ready "propext"
        , w `Effect4.Supervision.waitReplay_frontier "propext"
        , w `Effect4.Supervision.waitReplay_cons_ok "propext"
        , w `Effect4.Supervision.waitReplay_cons_error "propext"
        , w `Effect4.Supervision.wait_fixedTape_deterministic "propext"
        , w `Effect4.Supervision.waitReplay_done_ready "propext"
        , w `Effect4.Supervision.waitReplay_frame "propext,Quot.sound"
        , w `Effect4.Supervision.wait_two_publications "propext,Quot.sound"
        , w `Effect4.Supervision.raceForkOptions_eq "none"
        , w `Effect4.Supervision.raceCleanupMask_eq "none"
        , w `Effect4.Supervision.RaceAllState.initial_eq "none"
        , w `Effect4.Supervision.raceAllAdmit_eq "none"
        , w `Effect4.Supervision.RaceAllState.result_eq "propext"
        , w `Effect4.Supervision.raceComplete_unknown "propext"
        , w `Effect4.Supervision.raceComplete_after_accepted "propext,Quot.sound"
        , w `Effect4.Supervision.raceComplete_success "propext,Quot.sound"
        , w `Effect4.Supervision.raceComplete_failure_last "propext,Quot.sound"
        , w `Effect4.Supervision.raceComplete_failure_pending "propext,Quot.sound"
        , w `Effect4.Supervision.raceStep_begin_blocked "propext"
        , w `Effect4.Supervision.raceStep_begin_empty "propext"
        , w `Effect4.Supervision.raceStep_begin "propext"
        , w `Effect4.Supervision.raceStep_finish_missing "propext"
        , w `Effect4.Supervision.raceStep_finish_duplicate "propext"
        , w `Effect4.Supervision.raceStep_finish_live "propext"
        , w `Effect4.Supervision.raceStep_finish_done "propext"
        , w `Effect4.Supervision.raceStep_complete "propext"
        , w `Effect4.Supervision.raceStep_complete_unknown "propext"
        , w `Effect4.Supervision.raceStep_beginCleanup "propext"
        , w `Effect4.Supervision.raceStep_beginCleanup_blocked "propext"
        , w `Effect4.Supervision.raceStep_requestNext "propext"
        , w `Effect4.Supervision.raceStep_requestNext_blocked "propext"
        , w `Effect4.Supervision.raceStep_iff "propext"
        , w `Effect4.Supervision.raceRuns_iff "propext"
        , w `Effect4.Supervision.raceReplay_ready "propext"
        , w `Effect4.Supervision.raceReplay_frontier "propext"
        , w `Effect4.Supervision.raceReplay_cons_ok "propext"
        , w `Effect4.Supervision.raceReplay_cons_error "propext"
        , w `Effect4.Supervision.race_fixedTape_deterministic "propext"
        , w `Effect4.Supervision.race_first_accepted_stable "propext,Quot.sound"
        , w `Effect4.Supervision.race_result_requires_start_finished "propext"
        , w `Effect4.Supervision.race_cleanup_result_requires_publications "propext,Quot.sound"
        , w `Effect4.Supervision.race_empty_frontier "propext"
        , w `Effect4.Supervision.race_single_success "propext,Quot.sound"
        , w `Effect4.Supervision.race_two_failures "propext,Quot.sound" ] }
  , { id := "fork.await-all-children", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.newChildren_eq "propext"
        , w `Effect4.Supervision.newChildren_membership "propext,Quot.sound"
        , w `Effect4.Supervision.awaitAllChildren_eq "propext" ] }
  , { id := "fork.fiber-run-in", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.ScopeMode.cases_receipt "propext"
        , w `Effect4.Supervision.bindScope_invalid "propext"
        , w `Effect4.Supervision.bindScope_done "propext"
        , w `Effect4.Supervision.bindScope_closed "propext"
        , w `Effect4.Supervision.bindScope_duplicate_key "propext"
        , w `Effect4.Supervision.bindScope_open "propext"
        , w `Effect4.Supervision.scopeFinalizerInterruptor_eq "none"
        , w `Effect4.Supervision.scopeFinalizer_self_guard "propext"
        , w `Effect4.Supervision.scopeObserver_eq "none"
        , w `Effect4.Supervision.scopeObserver_key_membership "propext,Quot.sound" ] }
  , { id := "fork.join", kind := "fork", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.join_agreement "propext"
        , w `Effect4.double_join_agreement "propext"
        , w `Effect4.Supervision.ObserverMode.cases_receipt "propext"
        , w `Effect4.Supervision.Fiber.valid_iff "none"
        , w `Effect4.Supervision.Fiber.valid?_iff "propext"
        , w `Effect4.Supervision.Fiber.toFiberState_eq "none"
        , w `Effect4.Supervision.Fiber.published_iff "propext"
        , w `Effect4.Supervision.Fiber.published_eq "none"
        , w `Effect4.Supervision.observation_join "none"
        , w `Effect4.Supervision.observation_value_ne_effect "none"
        , w `Effect4.Supervision.Fiber.observe_invalid "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.observe_done "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.observe_live "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.observe_duplicate "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.cancel_eq "none"
        , w `Effect4.Supervision.Fiber.cancel_membership "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.publish_eq "none"
        , w `Effect4.Supervision.Fiber.publish_valid "propext" ] }
  , { id := "fork.await", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.ObserverMode.cases_receipt "propext"
        , w `Effect4.Supervision.Fiber.published_iff "propext"
        , w `Effect4.Supervision.Fiber.published_eq "none"
        , w `Effect4.Supervision.observation_await "none"
        , w `Effect4.Supervision.observation_value_ne_effect "none"
        , w `Effect4.Supervision.Fiber.observe_invalid "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.observe_done "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.observe_live "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.observe_duplicate "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.cancel_eq "none"
        , w `Effect4.Supervision.Fiber.cancel_membership "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.publish_eq "none"
        , w `Effect4.Supervision.Fiber.publish_valid "propext" ] }
  -- Remaining source clause: Request delivery, synchronous execution, and interruption followed by
  -- actual await. See SUPERVISION-PG-RC112.
  , { id := "fork.interrupt", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.interruptCause_eq "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.recordInterrupt_done "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.recordInterrupt_live "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.recordInterrupt_core "propext,Quot.sound"
        , w `Effect4.Supervision.interruptAllRequests_eq "none"
        , w `Effect4.Supervision.interruptAllWait_eq "none" ] }
  -- Remaining source clause: Executing request calls in order before explicit await; observations
  -- may arrive during calls. See SUPERVISION-PG-RC112.
  , { id := "fork.interrupt-all", kind := "fork", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.WaitState.begin_eq "none"
        , w `Effect4.Supervision.WaitState.pending_eq "propext"
        , w `Effect4.Supervision.WaitState.ready_iff "propext"
        , w `Effect4.Supervision.WaitState.ready_publications "propext,Quot.sound"
        , w `Effect4.Supervision.WaitState.observe_pending "propext"
        , w `Effect4.Supervision.WaitState.observe_unknown "propext"
        , w `Effect4.Supervision.WaitState.observe_pending_membership "propext,Quot.sound"
        , w `Effect4.Supervision.waitStep_iff "propext"
        , w `Effect4.Supervision.waitRuns_iff "propext"
        , w `Effect4.Supervision.waitReplay_ready "propext"
        , w `Effect4.Supervision.waitReplay_frontier "propext"
        , w `Effect4.Supervision.waitReplay_cons_ok "propext"
        , w `Effect4.Supervision.waitReplay_cons_error "propext"
        , w `Effect4.Supervision.wait_fixedTape_deterministic "propext"
        , w `Effect4.Supervision.waitReplay_done_ready "propext"
        , w `Effect4.Supervision.waitReplay_frame "propext,Quot.sound"
        , w `Effect4.Supervision.wait_two_publications "propext,Quot.sound"
        , w `Effect4.Supervision.interruptAllRequests_eq "none"
        , w `Effect4.Supervision.interruptAllWait_eq "none" ] }
  , { id := "scope.states", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.ScopeState.cases_receipt "none"
        , w `Effect4.ScopeState.entries_empty "none"
        , w `Effect4.ScopeState.entries_openEmpty "none"
        , w `Effect4.ScopeState.entries_openInline "none"
        , w `Effect4.ScopeState.entries_openMap "none"
        , w `Effect4.ScopeState.entries_closed "none"
        , w `Effect4.ScopeState.isOpen_empty "none"
        , w `Effect4.ScopeState.isOpen_openEmpty "none"
        , w `Effect4.ScopeState.isOpen_openInline "none"
        , w `Effect4.ScopeState.isOpen_openMap "none"
        , w `Effect4.ScopeState.isOpen_closed "none"
        , w `Effect4.ScopeState.isClosed_eq "none"
        , w `Effect4.ScopeState.closingExit_closed "none"
        , w `Effect4.ScopeState.closingExit_of_not_closed "none"
        , w `Effect4.ScopeState.openEmpty_ne_openMap_nil "none"
        , w `Effect4.Scope.finalizers_eq "none"
        , w `Effect4.Scope.finalizerKeys_eq "none"
        , w `Effect4.Scope.finalizerCount_eq "none"
        , w `Effect4.Scope.finalizerCount_not_open "none" ] }
  , { id := "scope.make", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FinalizerStrategy.all_nodup "none"
        , w `Effect4.FinalizerStrategy.mem_all "propext"
        , w `Effect4.Scope.make_strategy "none"
        , w `Effect4.Scope.make_state "none"
        , w `Effect4.Scope.make_finalizers "none"
        , w `Effect4.Scope.makeDefault_eq "none"
        , w `Effect4.Scope.makeDefault_strategy "none" ] }
  , { id := "scope.add-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.key_freshness_refused "none"
        , w `Effect4.Scope.tableInsert_new "propext,Quot.sound"
        , w `Effect4.Scope.tableInsert_existing "propext,Quot.sound"
        , w `Effect4.Scope.tableInsert_keys_of_mem "propext,Quot.sound"
        , w `Effect4.Scope.tableInsert_nodup "propext,Quot.sound"
        , w `Effect4.Scope.addUnsafe_strategy "none"
        , w `Effect4.Scope.addUnsafe_empty "none"
        , w `Effect4.Scope.addUnsafe_openEmpty "none"
        , w `Effect4.Scope.addUnsafe_openInline "none"
        , w `Effect4.Scope.addUnsafe_openMap "none"
        , w `Effect4.Scope.addUnsafe_promotes "propext,Quot.sound"
        , w `Effect4.Scope.addUnsafe_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.addUnsafe_keys_nodup "propext,Quot.sound" ] }
  , { id := "scope.add-after-closed", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.addUnsafe_closed "none"
        , w `Effect4.Scope.addExit_open "none"
        , w `Effect4.Scope.addExit_closed "none"
        , w `Effect4.Scope.addExit_closed_registers_nothing "none" ] }
  , { id := "scope.remove-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.tableRemove_eq "none"
        , w `Effect4.Scope.tableRemove_keys "propext,Quot.sound"
        , w `Effect4.Scope.tableRemove_nodup "propext"
        , w `Effect4.Scope.removeUnsafe_strategy "none"
        , w `Effect4.Scope.removeUnsafe_inline_hit "none"
        , w `Effect4.Scope.removeUnsafe_inline_miss "none"
        , w `Effect4.Scope.removeUnsafe_openMap "none"
        , w `Effect4.Scope.removeUnsafe_not_open "none"
        , w `Effect4.Scope.removeUnsafe_keys "propext,Quot.sound"
        , w `Effect4.Scope.removeUnsafe_keys_nodup "propext" ] }
  , { id := "scope.close-state-first", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.close_eq "none"
        , w `Effect4.Scope.close_state_independent_of_run "none"
        , w `Effect4.Scope.closeState_state "none"
        , w `Effect4.Scope.closeState_strategy "none"
        , w `Effect4.Scope.closeState_finalizers "none"
        , w `Effect4.Scope.closeState_isClosed "none"
        , w `Effect4.Scope.closeState_idempotent "none"
        , w `Effect4.Scope.close_closingExit "none"
        , w `Effect4.Scope.close_idempotent "none"
        , w `Effect4.Scope.close_twice "none"
        , w `Effect4.Scope.close_reentrant_add "none"
        , w `Effect4.Scope.closeResult_closed "none" ] }
  , { id := "scope.close-lifo", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.closeOrder_eq "none"
        , w `Effect4.Scope.closeOrder_last_first "propext"
        , w `Effect4.Scope.closeExits_eq "none"
        , w `Effect4.Scope.closeExits_reverse "propext"
        , w `Effect4.Scope.runScoped_lifo "propext,Quot.sound" ] }
  , { id := "scope.close-sequential", kind := "scope", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "awaits each finalizer through exit()" is temporal sequencing, a fiber-machine fact
    , witnesses :=
        [ w `Effect4.Scope.closeExits_eq "none"
        , w `Effect4.Scope.closeExits_length "propext"
        , w `Effect4.Scope.closeResult_reasons "propext" ] }
  , { id := "scope.close-parallel", kind := "scope", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "immediate daemon forks that inherit the closing fiber mask" is a fiber-machine fact
    , witnesses :=
        [ w `Effect4.FinalizerStrategy.cases_receipt "none"
        , w `Effect4.Scope.close_strategy_irrelevant "none" ] }
  , { id := "scope.close-merge", kind := "scope", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "parallel finalizer fibers are awaited together" is a fiber-machine fact
    , witnesses :=
        [ w `Effect4.Scope.closeResult_nil "none"
        , w `Effect4.Scope.closeResult_single "none"
        , w `Effect4.Scope.closeResult_many "none"
        , w `Effect4.Scope.closeResult_reasons "propext" ] }
  , { id := "scope.exit-as-void-all", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Exit.asVoidAll_reasons "none"
        , w `Effect4.Exit.asVoidAll_failure "none"
        , w `Effect4.Exit.asVoidAll_all_success "propext"
        , w `Effect4.Exit.void_eq "none" ] }
  , { id := "scope.fork-linkage", kind := "scope", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: that the linked names are scopeClose(child, exit) and scopeRemoveFinalizerUnsafe(parent, key) needs a scope store
    , witnesses :=
        [ w `Effect4.Scope.fork_closed_parent "none"
        , w `Effect4.Scope.fork_closed_parent_child_exit "none"
        , w `Effect4.Scope.fork_open_parent "none"
        , w `Effect4.Scope.fork_child_finalizers "none"
        , w `Effect4.Scope.fork_parent_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.fork_child_strategy "none"
        , w `Effect4.Scope.fork_shared_key "propext,Quot.sound"
        , w `Effect4.Scope.fork_detach "propext,Quot.sound" ] }
  , { id := "scope.scoped", kind := "scope", disposition := "separateCalculus", coverage := "partial"
      -- missing clauses: "installs a fresh scope in the fiber context" and "restoring the previous context first"
    , witnesses :=
        [ w `Effect4.Scope.addAll_nil "none"
        , w `Effect4.Scope.addAll_cons "none"
        , w `Effect4.Scope.addAll_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.make_addAll_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.runScoped_eq "none"
        , w `Effect4.Scope.runScoped_fresh_scope "none"
        , w `Effect4.Scope.runScoped_state "none"
        , w `Effect4.Scope.runScoped_strategy "none"
        , w `Effect4.Scope.runScoped_empty "none"
        , w `Effect4.Scope.runScoped_lifo "propext,Quot.sound"
        , w `Effect4.Prim.scopedFrame_eq "none"
        , w `Effect4.Prim.scopedFrame_finalizer_masked "propext"
        , w `Effect4.FrameFiber.step_scopedFrame "propext" ] }
  , { id := "scope.acquire-release", kind := "scope", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "with the captured context" needs a Context carrier
    , witnesses :=
        [ w `Effect4.Scope.acquireRelease_failure "none"
        , w `Effect4.Scope.acquireRelease_success "none"
        , w `Effect4.Scope.acquireRelease_registers "propext,Quot.sound"
        , w `Effect4.Scope.acquireRelease_closed_ambient "none"
        , w `Effect4.FrameFiber.uninterruptible_already_masked "propext"
        , w `Effect4.FrameFiber.uninterruptible_masks "propext"
        , w `Effect4.FrameFiber.uninterruptibleMask_eq "none"
        , w `Effect4.FrameFiber.interruptibleRegion_already "propext"
        , w `Effect4.FrameFiber.interruptibleRegion_masked "propext"
        , w `Effect4.FrameFiber.restoreAcquire_asked "none"
        , w `Effect4.FrameFiber.restoreAcquire_not_asked "none" ] }
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
  , { id := "exit.success-failure", kind := "exit", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Exit.cases_receipt "none"
        , w `Effect4.Exit.success_ne_failure "none"
        , w `Effect4.Exit.success_inj "none"
        , w `Effect4.Exit.failure_inj "none"
        , w `Effect4.Exit.cause_failure "none"
        , w `Effect4.Prim.ofExit_asExit? "none"
        , w `Effect4.Prim.asExit?_success "none"
        , w `Effect4.Prim.asExit?_failure "none"
        , w `Effect4.Prim.asExit?_eq_some "propext"
        , w `Effect4.Prim.ofExit_isFrame "none"
        , w `Effect4.FrameFiber.step_ofExit_finishes "propext"
        , w `Effect4.FrameFiber.run_zero "propext"
        , w `Effect4.FrameFiber.run_succ_finished "propext"
        , w `Effect4.FrameFiber.run_succ_running "propext" ] }
  , { id := "exit.reason-alphabet", kind := "exit", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.ReasonTag.all_nodup "none"
        , w `Effect4.ReasonTag.mem_all "propext"
        , w `Effect4.ReasonTag.cases_receipt "none"
        , w `Effect4.Reason.cases_receipt "none"
        , w `Effect4.Reason.tag_mem_all "propext" ] }
  , { id := "cause.flat-reasons", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.eq_iff "none"
        , w `Effect4.Cause.ext "none"
        , w `Effect4.Cause.eq_iff_pointwise "propext"
        , w `Effect4.Cause.combine_no_new_reason "propext" ] }
  , { id := "cause.reason-fail", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Reason.error_fail "none"
        , w `Effect4.Reason.annotations_fail "none"
        , w `Effect4.Reason.fail_inj "none" ] }
  , { id := "cause.reason-die", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Reason.defect_die "none"
        , w `Effect4.Reason.annotations_die "none"
        , w `Effect4.Reason.die_inj "none" ] }
  , { id := "cause.reason-interrupt", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.interrupt_reasons "none"
        , w `Effect4.Reason.annotations_interrupt "none"
        , w `Effect4.Reason.interrupt_inj "none" ] }
  , { id := "cause.combine-union", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.combine_empty_left "none"
        , w `Effect4.Cause.combine_empty_right "none"
        , w `Effect4.Cause.combine_reasons "none"
        , w `Effect4.Cause.mem_combine "propext"
        , w `Effect4.Cause.combine_self "propext,Quot.sound" ] }
  , { id := "cause.finalizer-merge", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Exit.mergeFinalizer_failure_failure "none"
        , w `Effect4.Exit.restoreAfterFinalizer_failure_failure "none"
        , w `Effect4.Exit.mergeFinalizer_success_failure "none"
        , w `Effect4.Exit.restoreAfterFinalizer_success_failure "none" ] }
  , { id := "cause.squash", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.squash_error "none"
        , w `Effect4.Cause.squash_defect "none"
        , w `Effect4.Cause.squash_interrupted "none"
        , w `Effect4.Cause.squash_emptyCause_iff "none"
        , w `Effect4.Cause.squash_fail_over_die "none" ] }
  , { id := "cause.union-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.combine_empty_left "none"
        , w `Effect4.Cause.combine_empty_right "none"
        , w `Effect4.Cause.combine_reasons "none"
        , w `Effect4.Cause.combine_order "propext,Quot.sound" ] }
  , { id := "cause.dedupe-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.dedup_cons "none"
        , w `Effect4.Cause.mem_dedup "propext"
        , w `Effect4.Cause.dedup_nodup "propext"
        , w `Effect4.Cause.dedup_of_nodup "propext,Quot.sound" ] }
  , { id := "cause.annotations", kind := "cause", disposition := "foreignBoundary", coverage := "green"
      -- the WeakMap host-identity clause is closed by refusal, not by a model
    , witnesses :=
        [ w `Effect4.ReasonAnnotations.keys_nodup "none"
        , w `Effect4.Reason.annotate_annotations "propext,Quot.sound"
        , w `Effect4.Reason.host_memory_refused "none"
        , w `Effect4.ReasonAnnotations.annotate_entries "propext,Quot.sound"
        , w `Effect4.ReasonAnnotations.lookup_annotate_kept "propext,Quot.sound"
        , w `Effect4.ReasonAnnotations.lookup_annotate_overwrite "propext,Quot.sound" ] }
  , { id := "entry.run-fork-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.abort-signal", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-callback-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-promise-exit-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-promise-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.run-sync-exit-with", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.async-fiber-error", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "entry.with-error-reporting", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "rule.frames-are-primitives", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Arm.all_nodup "none"
        , w `Effect4.Arm.mem_all "propext"
        , w `Effect4.Arm.cases_receipt "none"
        , w `Effect4.Arm.demandable_eq "none"
        , w `Effect4.Arm.contAll_not_demandable "propext"
        , w `Effect4.Prim.cases_receipt "none"
        , w `Effect4.FrameFiber.start_eq "none"
        , w `Effect4.FrameFiber.masked_eq "none"
        , w `Effect4.FrameFiber.interrupted_eq "none"
        , w `Effect4.FrameEvent.poppedFrames_nil "none"
        , w `Effect4.FrameEvent.poppedFrames_cons_popped "none"
        , w `Effect4.FrameEvent.finalizersRun_nil "none"
        , w `Effect4.FrameEvent.finalizersRun_cons_ran "none"
        , w `Effect4.FrameEvent.finalizersRun_cons_popped "none"
        , w `Effect4.Prim.hasArm_eq "none"
        , w `Effect4.Prim.isFrame_eq "none"
        , w `Effect4.Prim.isFrame_iff "propext"
        , w `Effect4.Prim.non_frames_have_no_arms "none"
        , w `Effect4.Prim.answerOf_replacement "none"
        , w `Effect4.Prim.answerOf_arm "propext"
        , w `Effect4.Prim.answerOf_missing "propext"
        , w `Effect4.Prim.answerOf_frame_eq "propext"
        , w `Effect4.Prim.armA_isSome "propext"
        , w `Effect4.Prim.armE_isSome "none"
        , w `Effect4.FrameFiber.getCont_eq_popFrom "propext"
        , w `Effect4.FrameFiber.getCont_empty_stack "propext"
        , w `Effect4.FrameFiber.popFrom_nil "propext"
        , w `Effect4.FrameFiber.popFrom_answer_answer "propext"
        , w `Effect4.FrameFiber.popFrom_answer_popped "propext"
        , w `Effect4.FrameFiber.popFrom_answer_events "propext"
        , w `Effect4.FrameFiber.popFrom_answer_fiber "propext"
        , w `Effect4.FrameFiber.popFrom_continue_answer "propext"
        , w `Effect4.FrameFiber.popFrom_continue_popped "propext"
        , w `Effect4.FrameFiber.popFrom_continue_events "propext"
        , w `Effect4.FrameFiber.popFrom_continue_fiber "propext"
        , w `Effect4.FrameFiber.popFrom_answer_hasArm "propext"
        , w `Effect4.FrameFiber.getCont_answer_hasArm "propext"
        , w `Effect4.FrameFiber.passEvents_ranContAll "propext"
        , w `Effect4.FrameFiber.passEvents_poppedFrames "propext,Quot.sound"
        , w `Effect4.FrameFiber.popFrom_popped_eq_events "propext,Quot.sound"
        , w `Effect4.FrameFiber.popFrom_ranContAll "propext"
        , w `Effect4.FrameFiber.getCont_ranContAll "propext" ] }
  , { id := "rule.interrupt-bypasses-handlers", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.ensure_setInterruptible_flag "propext"
        , w `Effect4.FrameFiber.interrupt_skips_every_handler "propext,Quot.sound"
        , w `Effect4.FrameFiber.getCont_mask_stops_skip "propext"
        , w `Effect4.FrameFiber.step_failure "propext" ] }
  , { id := "rule.yield-is-overloaded", kind := "rule", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  -- Remaining source clause: Correspondence of all source fork call sites/options to the observed
  -- controller inputs. See SUPERVISION-PG-RC112.
  , { id := "rule.only-fork-child-tracks", kind := "rule", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.Globals.ownsChildren_iff "none"
        , w `Effect4.Supervision.Fiber.addChild_eq "propext"
        , w `Effect4.Supervision.Fiber.removeChild_eq "none"
        , w `Effect4.Supervision.Fiber.addChild_nodup "propext,Quot.sound"
        , w `Effect4.Supervision.Fiber.removeChild_membership "propext,Quot.sound"
        , w `Effect4.Supervision.commitFork_eq "propext"
        , w `Effect4.Supervision.forkUnsafe_parent_children_nodup "propext,Quot.sound"
        , w `Effect4.Supervision.forkDetach_eq "propext"
        , w `Effect4.Supervision.commitFork_daemon_untracked "propext"
        , w `Effect4.Supervision.raceForkOptions_eq "none" ] }
  -- Remaining source clause: Parent continuation after a successful child wait; intervening
  -- interruption can replace the local body Exit. See SUPERVISION-PG-RC112.
  , { id := "rule.children-interrupted-after-exit", kind := "rule", disposition := "separateCalculus", coverage := "partial"
    , witnesses :=
        [ w `Effect4.Supervision.Globals.install_eq "none"
        , w `Effect4.Supervision.Fiber.published_iff "propext"
        , w `Effect4.Supervision.Fiber.publish_eq "none"
        , w `Effect4.Supervision.forkChild_eq "propext"
        , w `Effect4.Supervision.WaitState.begin_eq "none"
        , w `Effect4.Supervision.WaitState.pending_eq "propext"
        , w `Effect4.Supervision.WaitState.ready_iff "propext"
        , w `Effect4.Supervision.WaitState.ready_publications "propext,Quot.sound"
        , w `Effect4.Supervision.WaitState.observe_pending "propext"
        , w `Effect4.Supervision.WaitState.observe_unknown "propext"
        , w `Effect4.Supervision.WaitState.observe_pending_membership "propext,Quot.sound"
        , w `Effect4.Supervision.waitStep_iff "propext"
        , w `Effect4.Supervision.waitRuns_iff "propext"
        , w `Effect4.Supervision.ReplayResult.state_done "none"
        , w `Effect4.Supervision.ReplayResult.state_frontier "none"
        , w `Effect4.Supervision.ReplayResult.state_refused "none"
        , w `Effect4.Supervision.waitReplay_ready "propext"
        , w `Effect4.Supervision.waitReplay_frontier "propext"
        , w `Effect4.Supervision.waitReplay_cons_ok "propext"
        , w `Effect4.Supervision.waitReplay_cons_error "propext"
        , w `Effect4.Supervision.wait_fixedTape_deterministic "propext"
        , w `Effect4.Supervision.waitReplay_done_ready "propext"
        , w `Effect4.Supervision.waitReplay_frame "propext,Quot.sound"
        , w `Effect4.Supervision.wait_two_publications "propext,Quot.sound"
        , w `Effect4.Supervision.beginParentExit_eq "none"
        , w `Effect4.Supervision.parentExitView_waiting "propext"
        , w `Effect4.Supervision.parentExitView_ready "propext"
        , w `Effect4.Supervision.parentExitView_not_published_while_waiting "propext"
        , w `Effect4.Supervision.parentExitView_publication_requires_children "propext,Quot.sound" ] }
  , { id := "rule.scope-close-lifo-state-first", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.close_state_independent_of_run "none"
        , w `Effect4.Scope.closeState_finalizers "none"
        , w `Effect4.Scope.close_reentrant_add "none"
        , w `Effect4.Scope.closeOrder_last_first "propext"
        , w `Effect4.Scope.closeExits_reverse "propext" ] }
  , { id := "rule.cause-has-no-structure", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.mem_combine "propext"
        , w `Effect4.Cause.combine_order "propext,Quot.sound"
        , w `Effect4.Cause.combine_no_new_reason "propext"
        , w `Effect4.Cause.ext "none" ] }
  , { id := "rule.start-is-asymmetric", kind := "rule", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "rule.record-and-apply-separate", kind := "rule", disposition := "owned", coverage := "partial"
    , witnesses :=
        [ w `Effect4.masked_interrupt_defers "propext"
        , w `Effect4.unmask_delivers_pending "propext" ] }
  , { id := "rule.budget-per-runloop-entry", kind := "rule", disposition := "targetOnly", coverage := "absent", witnesses := [] }
    -- Host structures with no Lean carrier yet: `Effect4/Stateful/Ref.lean`,
    -- `Effect4/Stateful/Deferred.lean` and `Effect4/Layer/*.lean` are breadth
    -- stubs, so every row below is `absent` by construction. The five
    -- `derivedExpansion` rows are the ones the pinned source itself defines
    -- in terms of another pinned operation; the rest are `separateCalculus`.
  , { id := "ref.make", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.get", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.set-void-returns-cell", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.cell-set-returns-self", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.get-and-set", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.set-and-get-assignment", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.update", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.modify", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "ref.modify-some-no-reread", kind := "ref", disposition := "derivedExpansion", coverage := "absent", witnesses := [] }
  , { id := "ref.update-some-and-get-reread", kind := "ref", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.make", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.is-done", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.await", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.single-completion", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.completion-order", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.complete-with-stores-effect", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.done-is-complete-with", kind := "deferred", disposition := "derivedExpansion", coverage := "absent", witnesses := [] }
  , { id := "deferred.complete-runs-once", kind := "deferred", disposition := "derivedExpansion", coverage := "absent", witnesses := [] }
  , { id := "deferred.into-uninterruptible", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "deferred.interrupt", kind := "deferred", disposition := "derivedExpansion", coverage := "absent", witnesses := [] }
  , { id := "deferred.interrupt-with", kind := "deferred", disposition := "derivedExpansion", coverage := "absent", witnesses := [] }
  , { id := "deferred.poll", kind := "deferred", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.from-build-unsafe", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.from-build-child-scope", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.build-with-memo-map-service", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.memo-build-once", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.memo-finalizer-last-observer", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.memo-reuse-observer-count", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.memo-map-parent-lookup", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.memo-get-or-else", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.current-memo-map-fork-or-create", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.build-uses-ambient-scope", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.build-with-scope-still-forks-memo", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.merge-parallel-scopes", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.provide-dependency-first", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.fresh-drops-memoization", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.launch-holds-scope", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
  , { id := "layer.provide-effect-scope", kind := "layer", disposition := "separateCalculus", coverage := "absent", witnesses := [] }
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
  , `Effect4.Cause.eq_iff
  , `Effect4.Cause.ext
  , `Effect4.Cause.eq_iff_pointwise
  , `Effect4.Cause.combine_no_new_reason
  , `Effect4.Reason.error_fail
  , `Effect4.Reason.annotations_fail
  , `Effect4.Reason.fail_inj
  , `Effect4.Reason.defect_die
  , `Effect4.Reason.annotations_die
  , `Effect4.Reason.die_inj
  , `Effect4.Cause.interrupt_reasons
  , `Effect4.Reason.annotations_interrupt
  , `Effect4.Reason.interrupt_inj
  , `Effect4.Cause.combine_empty_left
  , `Effect4.Cause.combine_empty_right
  , `Effect4.Cause.combine_reasons
  , `Effect4.Cause.mem_combine
  , `Effect4.Cause.combine_self
  , `Effect4.Cause.combine_order
  , `Effect4.Cause.dedup_cons
  , `Effect4.Cause.mem_dedup
  , `Effect4.Cause.dedup_nodup
  , `Effect4.Cause.dedup_of_nodup
  , `Effect4.Exit.mergeFinalizer_failure_failure
  , `Effect4.Exit.restoreAfterFinalizer_failure_failure
  , `Effect4.Exit.mergeFinalizer_success_failure
  , `Effect4.Exit.restoreAfterFinalizer_success_failure
  , `Effect4.Cause.squash_error
  , `Effect4.Cause.squash_defect
  , `Effect4.Cause.squash_interrupted
  , `Effect4.Cause.squash_emptyCause_iff
  , `Effect4.Cause.squash_fail_over_die
  , `Effect4.ReasonAnnotations.keys_nodup
  , `Effect4.Reason.annotate_annotations
  , `Effect4.Reason.host_memory_refused
  , `Effect4.ReasonAnnotations.annotate_entries
  , `Effect4.ReasonAnnotations.lookup_annotate_kept
  , `Effect4.ReasonAnnotations.lookup_annotate_overwrite
  , `Effect4.Exit.cases_receipt
  , `Effect4.Exit.success_ne_failure
  , `Effect4.Exit.success_inj
  , `Effect4.Exit.failure_inj
  , `Effect4.Exit.cause_failure
  , `Effect4.ReasonTag.all_nodup
  , `Effect4.ReasonTag.mem_all
  , `Effect4.ReasonTag.cases_receipt
  , `Effect4.Reason.cases_receipt
  , `Effect4.Reason.tag_mem_all
  , `Effect4.Exit.asVoidAll_reasons
  , `Effect4.Exit.asVoidAll_failure
  , `Effect4.Exit.asVoidAll_all_success
  , `Effect4.Exit.void_eq
  , `Effect4.ScopeState.cases_receipt
  , `Effect4.ScopeState.entries_empty
  , `Effect4.ScopeState.entries_openEmpty
  , `Effect4.ScopeState.entries_openInline
  , `Effect4.ScopeState.entries_openMap
  , `Effect4.ScopeState.entries_closed
  , `Effect4.ScopeState.isOpen_empty
  , `Effect4.ScopeState.isOpen_openEmpty
  , `Effect4.ScopeState.isOpen_openInline
  , `Effect4.ScopeState.isOpen_openMap
  , `Effect4.ScopeState.isOpen_closed
  , `Effect4.ScopeState.isClosed_eq
  , `Effect4.ScopeState.closingExit_closed
  , `Effect4.ScopeState.closingExit_of_not_closed
  , `Effect4.ScopeState.openEmpty_ne_openMap_nil
  , `Effect4.Scope.finalizers_eq
  , `Effect4.Scope.finalizerKeys_eq
  , `Effect4.Scope.finalizerCount_eq
  , `Effect4.Scope.finalizerCount_not_open
  , `Effect4.FinalizerStrategy.all_nodup
  , `Effect4.FinalizerStrategy.mem_all
  , `Effect4.Scope.make_strategy
  , `Effect4.Scope.make_state
  , `Effect4.Scope.make_finalizers
  , `Effect4.Scope.makeDefault_eq
  , `Effect4.Scope.makeDefault_strategy
  , `Effect4.Scope.key_freshness_refused
  , `Effect4.Scope.tableInsert_new
  , `Effect4.Scope.tableInsert_existing
  , `Effect4.Scope.tableInsert_keys_of_mem
  , `Effect4.Scope.tableInsert_nodup
  , `Effect4.Scope.addUnsafe_strategy
  , `Effect4.Scope.addUnsafe_empty
  , `Effect4.Scope.addUnsafe_openEmpty
  , `Effect4.Scope.addUnsafe_openInline
  , `Effect4.Scope.addUnsafe_openMap
  , `Effect4.Scope.addUnsafe_promotes
  , `Effect4.Scope.addUnsafe_finalizers
  , `Effect4.Scope.addUnsafe_keys_nodup
  , `Effect4.Scope.addUnsafe_closed
  , `Effect4.Scope.addExit_open
  , `Effect4.Scope.addExit_closed
  , `Effect4.Scope.addExit_closed_registers_nothing
  , `Effect4.Scope.tableRemove_eq
  , `Effect4.Scope.tableRemove_keys
  , `Effect4.Scope.tableRemove_nodup
  , `Effect4.Scope.removeUnsafe_strategy
  , `Effect4.Scope.removeUnsafe_inline_hit
  , `Effect4.Scope.removeUnsafe_inline_miss
  , `Effect4.Scope.removeUnsafe_openMap
  , `Effect4.Scope.removeUnsafe_not_open
  , `Effect4.Scope.removeUnsafe_keys
  , `Effect4.Scope.removeUnsafe_keys_nodup
  , `Effect4.Scope.close_eq
  , `Effect4.Scope.close_state_independent_of_run
  , `Effect4.Scope.closeState_state
  , `Effect4.Scope.closeState_strategy
  , `Effect4.Scope.closeState_finalizers
  , `Effect4.Scope.closeState_isClosed
  , `Effect4.Scope.closeState_idempotent
  , `Effect4.Scope.close_closingExit
  , `Effect4.Scope.close_idempotent
  , `Effect4.Scope.close_twice
  , `Effect4.Scope.close_reentrant_add
  , `Effect4.Scope.closeResult_closed
  , `Effect4.Scope.closeOrder_eq
  , `Effect4.Scope.closeOrder_last_first
  , `Effect4.Scope.closeExits_eq
  , `Effect4.Scope.closeExits_reverse
  , `Effect4.Scope.runScoped_lifo
  , `Effect4.Scope.closeExits_length
  , `Effect4.Scope.closeResult_reasons
  , `Effect4.FinalizerStrategy.cases_receipt
  , `Effect4.Scope.close_strategy_irrelevant
  , `Effect4.Scope.closeResult_nil
  , `Effect4.Scope.closeResult_single
  , `Effect4.Scope.closeResult_many
  , `Effect4.Scope.fork_closed_parent
  , `Effect4.Scope.fork_closed_parent_child_exit
  , `Effect4.Scope.fork_open_parent
  , `Effect4.Scope.fork_child_finalizers
  , `Effect4.Scope.fork_parent_finalizers
  , `Effect4.Scope.fork_child_strategy
  , `Effect4.Scope.fork_shared_key
  , `Effect4.Scope.fork_detach
  , `Effect4.Scope.addAll_nil
  , `Effect4.Scope.addAll_cons
  , `Effect4.Scope.addAll_finalizers
  , `Effect4.Scope.make_addAll_finalizers
  , `Effect4.Scope.runScoped_eq
  , `Effect4.Scope.runScoped_fresh_scope
  , `Effect4.Scope.runScoped_state
  , `Effect4.Scope.runScoped_strategy
  , `Effect4.Scope.runScoped_empty
  , `Effect4.Scope.acquireRelease_failure
  , `Effect4.Scope.acquireRelease_success
  , `Effect4.Scope.acquireRelease_registers
  , `Effect4.Scope.acquireRelease_closed_ambient
  , `Effect4.Supervision.MaskMode.select_interruptible
  , `Effect4.Supervision.MaskMode.select_uninterruptible
  , `Effect4.Supervision.MaskMode.select_inherit
  , `Effect4.Supervision.MaskMode.cases_receipt
  , `Effect4.Supervision.ObserverMode.cases_receipt
  , `Effect4.Supervision.ScopeMode.cases_receipt
  , `Effect4.Supervision.Globals.install_eq
  , `Effect4.Supervision.Globals.valid_iff
  , `Effect4.Supervision.Globals.ownsChildren_iff
  , `Effect4.Supervision.Fiber.valid_iff
  , `Effect4.Supervision.Fiber.valid?_iff
  , `Effect4.Supervision.Fiber.toFiberState_eq
  , `Effect4.Supervision.Fiber.published_iff
  , `Effect4.Supervision.Fiber.published_eq
  , `Effect4.Supervision.Fiber.addChild_eq
  , `Effect4.Supervision.Fiber.removeChild_eq
  , `Effect4.Supervision.Fiber.addChild_nodup
  , `Effect4.Supervision.Fiber.removeChild_membership
  , `Effect4.Supervision.observation_await
  , `Effect4.Supervision.observation_join
  , `Effect4.Supervision.observation_value_ne_effect
  , `Effect4.Supervision.Fiber.observe_invalid
  , `Effect4.Supervision.Fiber.observe_done
  , `Effect4.Supervision.Fiber.observe_live
  , `Effect4.Supervision.Fiber.observe_duplicate
  , `Effect4.Supervision.Fiber.cancel_eq
  , `Effect4.Supervision.Fiber.cancel_membership
  , `Effect4.Supervision.Fiber.publish_eq
  , `Effect4.Supervision.Fiber.publish_valid
  , `Effect4.Supervision.interruptCause_eq
  , `Effect4.Supervision.Fiber.recordInterrupt_done
  , `Effect4.Supervision.Fiber.recordInterrupt_live
  , `Effect4.Supervision.Fiber.recordInterrupt_core
  , `Effect4.Supervision.initialFiber_eq
  , `Effect4.Supervision.initialFiber_valid
  , `Effect4.Supervision.commitFork_eq
  , `Effect4.Supervision.forkUnsafe_duplicate
  , `Effect4.Supervision.forkUnsafe_deferred
  , `Effect4.Supervision.forkUnsafe_wrong_deferred
  , `Effect4.Supervision.forkUnsafe_wrong_immediate
  , `Effect4.Supervision.forkUnsafe_wrong_identity
  , `Effect4.Supervision.forkUnsafe_wrong_parent
  , `Effect4.Supervision.forkUnsafe_invalid_child
  , `Effect4.Supervision.forkUnsafe_invalid_parent
  , `Effect4.Supervision.forkUnsafe_invalid_globals
  , `Effect4.Supervision.forkUnsafe_invalid_ownership
  , `Effect4.Supervision.forkUnsafe_invalid_child_ownership
  , `Effect4.Supervision.forkUnsafe_immediate
  , `Effect4.Supervision.forkUnsafe_fresh
  , `Effect4.Supervision.forkUnsafe_allocated_nodup
  , `Effect4.Supervision.forkUnsafe_child_valid
  , `Effect4.Supervision.forkUnsafe_parent_children_nodup
  , `Effect4.Supervision.forkChild_eq
  , `Effect4.Supervision.forkDetach_eq
  , `Effect4.Supervision.commitFork_done_untracked
  , `Effect4.Supervision.commitFork_daemon_untracked
  , `Effect4.Supervision.Globals.allocate_eq
  , `Effect4.Supervision.Globals.extends_iff
  , `Effect4.Supervision.Globals.extends?_iff
  , `Effect4.Supervision.Globals.ownsChildren?_iff
  , `Effect4.Supervision.WaitState.begin_eq
  , `Effect4.Supervision.WaitState.pending_eq
  , `Effect4.Supervision.WaitState.ready_iff
  , `Effect4.Supervision.WaitState.ready_publications
  , `Effect4.Supervision.WaitState.observe_pending
  , `Effect4.Supervision.WaitState.observe_unknown
  , `Effect4.Supervision.WaitState.observe_pending_membership
  , `Effect4.Supervision.waitStep_iff
  , `Effect4.Supervision.waitRuns_iff
  , `Effect4.Supervision.ReplayResult.state_done
  , `Effect4.Supervision.ReplayResult.state_frontier
  , `Effect4.Supervision.ReplayResult.state_refused
  , `Effect4.Supervision.waitReplay_ready
  , `Effect4.Supervision.waitReplay_frontier
  , `Effect4.Supervision.waitReplay_cons_ok
  , `Effect4.Supervision.waitReplay_cons_error
  , `Effect4.Supervision.wait_fixedTape_deterministic
  , `Effect4.Supervision.waitReplay_done_ready
  , `Effect4.Supervision.waitReplay_frame
  , `Effect4.Supervision.wait_two_publications
  , `Effect4.Supervision.beginParentExit_eq
  , `Effect4.Supervision.parentExitView_waiting
  , `Effect4.Supervision.parentExitView_ready
  , `Effect4.Supervision.parentExitView_not_published_while_waiting
  , `Effect4.Supervision.parentExitView_publication_requires_children
  , `Effect4.Supervision.newChildren_eq
  , `Effect4.Supervision.newChildren_membership
  , `Effect4.Supervision.awaitAllChildren_eq
  , `Effect4.Supervision.interruptAllRequests_eq
  , `Effect4.Supervision.interruptAllWait_eq
  , `Effect4.Supervision.bindScope_invalid
  , `Effect4.Supervision.bindScope_done
  , `Effect4.Supervision.bindScope_closed
  , `Effect4.Supervision.bindScope_duplicate_key
  , `Effect4.Supervision.bindScope_open
  , `Effect4.Supervision.forkScopedBinding_eq
  , `Effect4.Supervision.scopeFinalizerInterruptor_eq
  , `Effect4.Supervision.scopeFinalizer_self_guard
  , `Effect4.Supervision.scopeObserver_eq
  , `Effect4.Supervision.scopeObserver_key_membership
  , `Effect4.Supervision.raceForkOptions_eq
  , `Effect4.Supervision.raceCleanupMask_eq
  , `Effect4.Supervision.RaceAllState.initial_eq
  , `Effect4.Supervision.raceAllAdmit_eq
  , `Effect4.Supervision.RaceAllState.result_eq
  , `Effect4.Supervision.raceComplete_unknown
  , `Effect4.Supervision.raceComplete_after_accepted
  , `Effect4.Supervision.raceComplete_success
  , `Effect4.Supervision.raceComplete_failure_last
  , `Effect4.Supervision.raceComplete_failure_pending
  , `Effect4.Supervision.raceStep_begin_blocked
  , `Effect4.Supervision.raceStep_begin_empty
  , `Effect4.Supervision.raceStep_begin
  , `Effect4.Supervision.raceStep_finish_missing
  , `Effect4.Supervision.raceStep_finish_duplicate
  , `Effect4.Supervision.raceStep_finish_live
  , `Effect4.Supervision.raceStep_finish_done
  , `Effect4.Supervision.raceStep_complete
  , `Effect4.Supervision.raceStep_complete_unknown
  , `Effect4.Supervision.raceStep_beginCleanup
  , `Effect4.Supervision.raceStep_beginCleanup_blocked
  , `Effect4.Supervision.raceStep_requestNext
  , `Effect4.Supervision.raceStep_requestNext_blocked
  , `Effect4.Supervision.raceStep_iff
  , `Effect4.Supervision.raceRuns_iff
  , `Effect4.Supervision.raceReplay_ready
  , `Effect4.Supervision.raceReplay_frontier
  , `Effect4.Supervision.raceReplay_cons_ok
  , `Effect4.Supervision.raceReplay_cons_error
  , `Effect4.Supervision.race_fixedTape_deterministic
  , `Effect4.Supervision.race_first_accepted_stable
  , `Effect4.Supervision.race_result_requires_start_finished
  , `Effect4.Supervision.race_cleanup_result_requires_publications
  , `Effect4.Supervision.race_empty_frontier
  , `Effect4.Supervision.race_single_success
  , `Effect4.Supervision.race_two_failures
  , `Effect4.Arm.all_nodup
  , `Effect4.Arm.mem_all
  , `Effect4.Arm.cases_receipt
  , `Effect4.Arm.demandable_eq
  , `Effect4.Arm.contAll_not_demandable
  , `Effect4.Prim.cases_receipt
  , `Effect4.FrameFiber.start_eq
  , `Effect4.FrameFiber.pendingCause_some
  , `Effect4.FrameFiber.pendingCause_none
  , `Effect4.FrameFiber.masked_eq
  , `Effect4.FrameFiber.interrupted_eq
  , `Effect4.FrameEvent.poppedFrames_nil
  , `Effect4.FrameEvent.poppedFrames_cons_popped
  , `Effect4.FrameEvent.finalizersRun_nil
  , `Effect4.FrameEvent.finalizersRun_cons_ran
  , `Effect4.FrameEvent.finalizersRun_cons_popped
  , `Effect4.Prim.hasArm_eq
  , `Effect4.Prim.isFrame_eq
  , `Effect4.Prim.isFrame_iff
  , `Effect4.Prim.arms_onSuccess
  , `Effect4.Prim.arms_onFailure
  , `Effect4.Prim.arms_onSuccessAndFailure
  , `Effect4.Prim.arms_exitFrame
  , `Effect4.Prim.arms_onExit
  , `Effect4.Prim.arms_setInterruptible
  , `Effect4.Prim.arms_whileLoop
  , `Effect4.Prim.arms_iterator
  , `Effect4.Prim.non_frames_have_no_arms
  , `Effect4.Prim.ofExit_asExit?
  , `Effect4.Prim.asExit?_success
  , `Effect4.Prim.asExit?_failure
  , `Effect4.Prim.asExit?_eq_some
  , `Effect4.Prim.ofExit_isFrame
  , `Effect4.Prim.ensure_of_no_contAll
  , `Effect4.Prim.ensure_onExit_masks
  , `Effect4.Prim.ensure_onExit_told_not_to
  , `Effect4.Prim.ensure_onExit_already_masked
  , `Effect4.Prim.ensure_onExit_no_replacement
  , `Effect4.Prim.ensure_setInterruptible_flag
  , `Effect4.Prim.ensure_setInterruptible_stack
  , `Effect4.Prim.ensure_setInterruptible_substitutes
  , `Effect4.Prim.ensure_setInterruptible_false_no_replacement
  , `Effect4.Prim.ensure_setInterruptible_no_pending
  , `Effect4.Prim.answerOf_replacement
  , `Effect4.Prim.answerOf_arm
  , `Effect4.Prim.answerOf_missing
  , `Effect4.Prim.answerOf_frame_eq
  , `Effect4.Prim.armA_isSome
  , `Effect4.Prim.armE_isSome
  , `Effect4.Prim.armA_onSuccess
  , `Effect4.Prim.armA_onSuccessAndFailure
  , `Effect4.Prim.armE_onFailure
  , `Effect4.Prim.armE_onSuccessAndFailure
  , `Effect4.Prim.armE_onSuccess_none
  , `Effect4.Prim.armA_onFailure_none
  , `Effect4.Prim.armA_setInterruptible_none
  , `Effect4.Prim.armE_setInterruptible_none
  , `Effect4.Prim.armE_whileLoop_none
  , `Effect4.Prim.armE_iterator_none
  , `Effect4.Prim.armA_exitFrame_provided
  , `Effect4.Prim.armA_exitFrame_none
  , `Effect4.Prim.armE_exitFrame_provided
  , `Effect4.Prim.armE_exitFrame_none
  , `Effect4.Prim.armA_onExit
  , `Effect4.Prim.armE_onExit
  , `Effect4.Prim.onExit_finalizer_success_restores
  , `Effect4.Prim.onExit_finalizer_failure_merges
  , `Effect4.Prim.onExit_success_finalizer_failure
  , `Effect4.Prim.onExit_arm_is_per_frame
  , `Effect4.Prim.onSuccess_arm_is_per_instance
  , `Effect4.Prim.onFailure_arm_is_per_instance
  , `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance
  , `Effect4.Prim.armA_whileLoop_continue
  , `Effect4.Prim.armA_whileLoop_stop
  , `Effect4.Prim.armA_iterator_done
  , `Effect4.Prim.armA_iterator_halt
  , `Effect4.Prim.armA_iterator_resume
  , `Effect4.Prim.iteratorFolded_eq
  , `Effect4.Prim.iterator_folds_inline
  , `Effect4.Prim.finalizerEvents_onExit
  , `Effect4.Prim.finalizerEvents_onSuccess
  , `Effect4.Prim.finalizerEvents_onFailure
  , `Effect4.FrameFiber.getCont_deferred
  , `Effect4.FrameFiber.getCont_deferred_pops_nothing
  , `Effect4.FrameFiber.getCont_eq_popFrom
  , `Effect4.FrameFiber.getCont_skip_clears_deferred
  , `Effect4.FrameFiber.getCont_empty_stack
  , `Effect4.FrameFiber.popFrom_nil
  , `Effect4.FrameFiber.popFrom_answer_answer
  , `Effect4.FrameFiber.popFrom_answer_popped
  , `Effect4.FrameFiber.popFrom_answer_events
  , `Effect4.FrameFiber.popFrom_answer_fiber
  , `Effect4.FrameFiber.popFrom_continue_answer
  , `Effect4.FrameFiber.popFrom_continue_popped
  , `Effect4.FrameFiber.popFrom_continue_events
  , `Effect4.FrameFiber.popFrom_continue_fiber
  , `Effect4.FrameFiber.popFrom_answer_hasArm
  , `Effect4.FrameFiber.getCont_answer_hasArm
  , `Effect4.FrameFiber.passEvents_ranContAll
  , `Effect4.FrameFiber.passEvents_poppedFrames
  , `Effect4.FrameFiber.popFrom_popped_eq_events
  , `Effect4.FrameFiber.popFrom_ranContAll
  , `Effect4.FrameFiber.getCont_ranContAll
  , `Effect4.FrameFiber.getCont_skip_of_no_pending_cause
  , `Effect4.FrameFiber.interrupt_skips_every_handler
  , `Effect4.FrameFiber.getCont_mask_stops_skip
  , `Effect4.FrameFiber.resumeValue_empty
  , `Effect4.FrameFiber.resumeValue_deferred
  , `Effect4.FrameFiber.resumeValue_replacement
  , `Effect4.FrameFiber.resumeValue_frame
  , `Effect4.FrameFiber.resumeCause_empty
  , `Effect4.FrameFiber.resumeCause_deferred
  , `Effect4.FrameFiber.resumeCause_replacement
  , `Effect4.FrameFiber.resumeCause_frame
  , `Effect4.FrameFiber.step_success
  , `Effect4.FrameFiber.step_failure
  , `Effect4.FrameFiber.step_sync
  , `Effect4.FrameFiber.step_suspend
  , `Effect4.FrameFiber.step_withFiber
  , `Effect4.FrameFiber.step_yieldableError
  , `Effect4.FrameFiber.step_onSuccess
  , `Effect4.FrameFiber.step_onFailure
  , `Effect4.FrameFiber.step_onSuccessAndFailure
  , `Effect4.FrameFiber.step_exitFrame
  , `Effect4.FrameFiber.step_onExit
  , `Effect4.FrameFiber.step_setInterruptible_not_evaluable
  , `Effect4.FrameFiber.step_whileLoop_true
  , `Effect4.FrameFiber.step_whileLoop_false
  , `Effect4.FrameFiber.step_iterator
  , `Effect4.FrameFiber.step_ofExit_finishes
  , `Effect4.FrameFiber.run_zero
  , `Effect4.FrameFiber.run_succ_finished
  , `Effect4.FrameFiber.run_succ_running
  , `Effect4.FrameFiber.uninterruptible_already_masked
  , `Effect4.FrameFiber.uninterruptible_masks
  , `Effect4.FrameFiber.uninterruptibleMask_eq
  , `Effect4.FrameFiber.setFiberInterruptible_flag
  , `Effect4.FrameFiber.setFiberInterruptible_pushes
  , `Effect4.FrameFiber.setFiberInterruptible_immediate_failure
  , `Effect4.FrameFiber.setFiberInterruptible_no_pending
  , `Effect4.FrameFiber.interruptibleRegion_already
  , `Effect4.FrameFiber.interruptibleRegion_masked
  , `Effect4.FrameFiber.restoreAcquire_asked
  , `Effect4.FrameFiber.restoreAcquire_not_asked
  , `Effect4.Prim.scopedFrame_eq
  , `Effect4.Prim.scopedFrame_finalizer_masked
  , `Effect4.FrameFiber.step_scopedFrame
  , `Effect4.Prim.withFiber_refused
  , `Effect4.Prim.yieldableError_host_class_refused
  ]

private def expectedRowTotal : Nat := 137
private def expectedDenominator : Nat := 117

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
