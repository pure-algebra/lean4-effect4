import Lean
import Lean.Util.CollectAxioms
import Effect4.Concurrency.Scheduler
import Effect4.Concurrency.Supervision

/-!
# Fiber representative declaration and proof-graph join

This test-only checker joins the exact three-module compiler-owned surface
to the frozen 185-name authored API, 92 public theorem receipts, exact
per-theorem kernel dependency expectations, 16 type dispositions, 14
passive-leaf receipt routes, duplicate-prevention names, and the existing
`FIBER-PG-REPRESENTATIVE` graph. It contains no manual closure flag.
-/

open Lean Elab Command

namespace Effect4Test.Concurrency.FiberAssurance

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"fiber assurance mismatch: {detail}"

private def declarationOwner? (environment : Environment) (name : Name) : Option Name := do
  if let some moduleIndex := environment.getModuleIdxFor? name then
    environment.header.moduleNames[moduleIndex]?
  else if environment.contains name then
    some environment.mainModule
  else
    none

private def declarationsOwnedBy (environment : Environment) (owner : Name) : List Name :=
  environment.constants.toList.foldl (init := []) fun declarations entry =>
    let name := entry.1
    if !name.isInternal && declarationOwner? environment name == some owner then
      name :: declarations
    else
      declarations

private def sameNameSet (actual expected : List Name) : Bool :=
  actual.length == expected.length &&
    actual.all expected.contains && expected.all actual.contains

private def firstDuplicateName? : List Name → Option Name
  | [] => none
  | name :: names =>
      if names.contains name then some name else firstDuplicateName? names

private def firstDuplicateString? : List String → Option String
  | [] => none
  | value :: values =>
      if values.contains value then some value else firstDuplicateString? values

private def checkUniqueNames (label : String) (names : List Name) : CommandElabM Unit := do
  if let some duplicate := firstDuplicateName? names then
    failJoin m!"duplicate {label} name: {duplicate}"

private def checkUniqueStrings (label : String) (values : List String) : CommandElabM Unit := do
  if let some duplicate := firstDuplicateString? values then
    failJoin m!"duplicate {label} identifier: {duplicate}"

private def checkOwners (expectedOwner : Name) (names : List Name) : CommandElabM Unit := do
  let environment ← getEnv
  for name in names do
    unless environment.contains name do
      failJoin m!"missing declaration {name}"
    let actualOwner := declarationOwner? environment name
    unless actualOwner == some expectedOwner do
      failJoin m!"owner drift for {name}: expected {expectedOwner}, found {actualOwner}"

private def checkExactModuleSurface
    (expectedOwner : Name) (expected : List Name) : CommandElabM Unit := do
  checkUniqueNames s!"owned declaration census for {expectedOwner}" expected
  checkOwners expectedOwner expected
  let actual := declarationsOwnedBy (← getEnv) expectedOwner
  checkUniqueNames s!"compiler declaration census for {expectedOwner}" actual
  let unexpected := actual.filter fun name => !expected.contains name
  let missing := expected.filter fun name => !actual.contains name
  unless unexpected.isEmpty && missing.isEmpty do
    failJoin m!"owned declaration census for {expectedOwner}: unexpected {unexpected}; missing {missing}"

private def expectedInterruptOwned : List Name :=
  [ `Effect4.CleanupState
  , `Effect4.CleanupState.casesOn
  , `Effect4.CleanupState.cases_receipt
  , `Effect4.CleanupState.ctorElim
  , `Effect4.CleanupState.ctorElimType
  , `Effect4.CleanupState.ctorIdx
  , `Effect4.CleanupState.done
  , `Effect4.CleanupState.done.elim
  , `Effect4.CleanupState.done.sizeOf_spec
  , `Effect4.CleanupState.noConfusion
  , `Effect4.CleanupState.noConfusionType
  , `Effect4.CleanupState.notStarted
  , `Effect4.CleanupState.notStarted.elim
  , `Effect4.CleanupState.notStarted.sizeOf_spec
  , `Effect4.CleanupState.ofNat
  , `Effect4.CleanupState.ofNat_ctorIdx
  , `Effect4.CleanupState.pending
  , `Effect4.CleanupState.pending.elim
  , `Effect4.CleanupState.pending.sizeOf_spec
  , `Effect4.CleanupState.rec
  , `Effect4.CleanupState.recOn
  , `Effect4.CleanupState.toCtorIdx
  , `Effect4.InterruptBoundary
  , `Effect4.InterruptBoundary.casesOn
  , `Effect4.InterruptBoundary.ctorIdx
  , `Effect4.InterruptBoundary.interrupted
  , `Effect4.InterruptBoundary.mk
  , `Effect4.InterruptBoundary.mk.inj
  , `Effect4.InterruptBoundary.mk.injEq
  , `Effect4.InterruptBoundary.mk.noConfusion
  , `Effect4.InterruptBoundary.mk.sizeOf_spec
  , `Effect4.InterruptBoundary.noConfusion
  , `Effect4.InterruptBoundary.noConfusionType
  , `Effect4.InterruptBoundary.rec
  , `Effect4.InterruptBoundary.recOn
  , `Effect4.InterruptMask
  , `Effect4.InterruptMask.casesOn
  , `Effect4.InterruptMask.cases_receipt
  , `Effect4.InterruptMask.ctorElim
  , `Effect4.InterruptMask.ctorElimType
  , `Effect4.InterruptMask.ctorIdx
  , `Effect4.InterruptMask.masked
  , `Effect4.InterruptMask.masked.elim
  , `Effect4.InterruptMask.masked.sizeOf_spec
  , `Effect4.InterruptMask.noConfusion
  , `Effect4.InterruptMask.noConfusionType
  , `Effect4.InterruptMask.ofNat
  , `Effect4.InterruptMask.ofNat_ctorIdx
  , `Effect4.InterruptMask.rec
  , `Effect4.InterruptMask.recOn
  , `Effect4.InterruptMask.toCtorIdx
  , `Effect4.InterruptMask.unmasked
  , `Effect4.InterruptMask.unmasked.elim
  , `Effect4.InterruptMask.unmasked.sizeOf_spec
  , `Effect4.instDecidableEqCleanupState
  , `Effect4.instDecidableEqInterruptMask
  , `Effect4.instReprCleanupState
  , `Effect4.instReprCleanupState.repr
  , `Effect4.instReprCleanupState.repr.match_1
  , `Effect4.instReprInterruptMask
  , `Effect4.instReprInterruptMask.repr
  , `Effect4.instReprInterruptMask.repr.match_1
  ]

private def expectedFiberOwned : List Name :=
  [ `Effect4.FiberId
  , `Effect4.FiberId.casesOn
  , `Effect4.FiberId.ctorIdx
  , `Effect4.FiberId.mk
  , `Effect4.FiberId.mk.inj
  , `Effect4.FiberId.mk.injEq
  , `Effect4.FiberId.mk.noConfusion
  , `Effect4.FiberId.mk.sizeOf_spec
  , `Effect4.FiberId.noConfusion
  , `Effect4.FiberId.noConfusionType
  , `Effect4.FiberId.rec
  , `Effect4.FiberId.recOn
  , `Effect4.FiberId.value
  , `Effect4.FiberState
  , `Effect4.FiberState.casesOn
  , `Effect4.FiberState.cleanup
  , `Effect4.FiberState.cleanupCount
  , `Effect4.FiberState.ctorIdx
  , `Effect4.FiberState.id
  , `Effect4.FiberState.interruptPending
  , `Effect4.FiberState.mask
  , `Effect4.FiberState.mk
  , `Effect4.FiberState.mk.inj
  , `Effect4.FiberState.mk.injEq
  , `Effect4.FiberState.mk.noConfusion
  , `Effect4.FiberState.mk.sizeOf_spec
  , `Effect4.FiberState.noConfusion
  , `Effect4.FiberState.noConfusionType
  , `Effect4.FiberState.rec
  , `Effect4.FiberState.recOn
  , `Effect4.FiberState.status
  , `Effect4.FiberState.terminal
  , `Effect4.FiberStatus
  , `Effect4.FiberStatus.Active
  , `Effect4.FiberStatus.Active.eq_1
  , `Effect4.FiberStatus.Active.eq_2
  , `Effect4.FiberStatus.Active.eq_3
  , `Effect4.FiberStatus.Active.eq_4
  , `Effect4.FiberStatus.Active.eq_5
  , `Effect4.FiberStatus.activeDecidable
  , `Effect4.FiberStatus.active_iff
  , `Effect4.FiberStatus.casesOn
  , `Effect4.FiberStatus.cases_receipt
  , `Effect4.FiberStatus.ctorElim
  , `Effect4.FiberStatus.ctorElimType
  , `Effect4.FiberStatus.ctorIdx
  , `Effect4.FiberStatus.done
  , `Effect4.FiberStatus.done.elim
  , `Effect4.FiberStatus.done.sizeOf_spec
  , `Effect4.FiberStatus.finalizing
  , `Effect4.FiberStatus.finalizing.elim
  , `Effect4.FiberStatus.finalizing.sizeOf_spec
  , `Effect4.FiberStatus.noConfusion
  , `Effect4.FiberStatus.noConfusionType
  , `Effect4.FiberStatus.rec
  , `Effect4.FiberStatus.recOn
  , `Effect4.FiberStatus.runnable
  , `Effect4.FiberStatus.runnable.elim
  , `Effect4.FiberStatus.runnable.sizeOf_spec
  , `Effect4.FiberStatus.running
  , `Effect4.FiberStatus.running.elim
  , `Effect4.FiberStatus.running.sizeOf_spec
  , `Effect4.FiberStatus.waiting
  , `Effect4.FiberStatus.waiting.elim
  , `Effect4.FiberStatus.waiting.inj
  , `Effect4.FiberStatus.waiting.injEq
  , `Effect4.FiberStatus.waiting.noConfusion
  , `Effect4.FiberStatus.waiting.sizeOf_spec
  , `Effect4.instDecidableEqFiberId
  , `Effect4.instDecidableEqFiberId.decEq
  , `Effect4.instDecidableEqFiberId.decEq.match_1
  , `Effect4.instDecidableEqFiberStatus
  , `Effect4.instDecidableEqFiberStatus.decEq
  , `Effect4.instDecidableEqFiberStatus.decEq.match_1
  , `Effect4.instReprFiberId
  , `Effect4.instReprFiberId.repr
  , `Effect4.instReprFiberStatus
  , `Effect4.instReprFiberStatus.repr
  , `Effect4.instReprFiberStatus.repr.match_1
  ]

private def expectedSchedulerOwned : List Name :=
  [ `Effect4.DecisionTape
  , `Effect4.Event
  , `Effect4.Event.casesOn
  , `Effect4.Event.cases_receipt
  , `Effect4.Event.cleanupFinished
  , `Effect4.Event.cleanupFinished.elim
  , `Effect4.Event.cleanupFinished.inj
  , `Effect4.Event.cleanupFinished.injEq
  , `Effect4.Event.cleanupFinished.noConfusion
  , `Effect4.Event.cleanupFinished.sizeOf_spec
  , `Effect4.Event.cleanupId?
  , `Effect4.Event.cleanupId?.eq_1
  , `Effect4.Event.cleanupId?.eq_2
  , `Effect4.Event.cleanupId?.match_1
  , `Effect4.Event.cleanupId_eq_some
  , `Effect4.Event.completed
  , `Effect4.Event.completed.elim
  , `Effect4.Event.completed.inj
  , `Effect4.Event.completed.injEq
  , `Effect4.Event.completed.noConfusion
  , `Effect4.Event.completed.sizeOf_spec
  , `Effect4.Event.ctorElim
  , `Effect4.Event.ctorElimType
  , `Effect4.Event.ctorIdx
  , `Effect4.Event.interruptDeferred
  , `Effect4.Event.interruptDeferred.elim
  , `Effect4.Event.interruptDeferred.inj
  , `Effect4.Event.interruptDeferred.injEq
  , `Effect4.Event.interruptDeferred.noConfusion
  , `Effect4.Event.interruptDeferred.sizeOf_spec
  , `Effect4.Event.interruptDelivered
  , `Effect4.Event.interruptDelivered.elim
  , `Effect4.Event.interruptDelivered.inj
  , `Effect4.Event.interruptDelivered.injEq
  , `Effect4.Event.interruptDelivered.noConfusion
  , `Effect4.Event.interruptDelivered.sizeOf_spec
  , `Effect4.Event.interruptRequested
  , `Effect4.Event.interruptRequested.elim
  , `Effect4.Event.interruptRequested.inj
  , `Effect4.Event.interruptRequested.injEq
  , `Effect4.Event.interruptRequested.noConfusion
  , `Effect4.Event.interruptRequested.sizeOf_spec
  , `Effect4.Event.joinObserved
  , `Effect4.Event.joinObserved.elim
  , `Effect4.Event.joinObserved.inj
  , `Effect4.Event.joinObserved.injEq
  , `Effect4.Event.joinObserved.noConfusion
  , `Effect4.Event.joinObserved.sizeOf_spec
  , `Effect4.Event.joinWaiting
  , `Effect4.Event.joinWaiting.elim
  , `Effect4.Event.joinWaiting.inj
  , `Effect4.Event.joinWaiting.injEq
  , `Effect4.Event.joinWaiting.noConfusion
  , `Effect4.Event.joinWaiting.sizeOf_spec
  , `Effect4.Event.maskEntered
  , `Effect4.Event.maskEntered.elim
  , `Effect4.Event.maskEntered.inj
  , `Effect4.Event.maskEntered.injEq
  , `Effect4.Event.maskEntered.noConfusion
  , `Effect4.Event.maskEntered.sizeOf_spec
  , `Effect4.Event.maskExited
  , `Effect4.Event.maskExited.elim
  , `Effect4.Event.maskExited.inj
  , `Effect4.Event.maskExited.injEq
  , `Effect4.Event.maskExited.noConfusion
  , `Effect4.Event.maskExited.sizeOf_spec
  , `Effect4.Event.noConfusion
  , `Effect4.Event.noConfusionType
  , `Effect4.Event.rec
  , `Effect4.Event.recOn
  , `Effect4.Event.scheduled
  , `Effect4.Event.scheduled.elim
  , `Effect4.Event.scheduled.inj
  , `Effect4.Event.scheduled.injEq
  , `Effect4.Event.scheduled.noConfusion
  , `Effect4.Event.scheduled.sizeOf_spec
  , `Effect4.Machine
  , `Effect4.Machine.Finished
  , `Effect4.Machine.WellFormed
  , `Effect4.Machine.WellFormed.activeCleanup
  , `Effect4.Machine.WellFormed.casesOn
  , `Effect4.Machine.WellFormed.cleanupBounded
  , `Effect4.Machine.WellFormed.cleanupEventAgreement
  , `Effect4.Machine.WellFormed.cleanupEventsClosed
  , `Effect4.Machine.WellFormed.cleanupEventsUnique
  , `Effect4.Machine.WellFormed.doneCleanup
  , `Effect4.Machine.WellFormed.finalizingCleanup
  , `Effect4.Machine.WellFormed.idsUnique
  , `Effect4.Machine.WellFormed.mk
  , `Effect4.Machine.WellFormed.pendingActive
  , `Effect4.Machine.WellFormed.rec
  , `Effect4.Machine.WellFormed.recOn
  , `Effect4.Machine.WellFormed.waitingClosed
  , `Effect4.Machine.casesOn
  , `Effect4.Machine.cleanupCount
  , `Effect4.Machine.cleanupCount.eq_1
  , `Effect4.Machine.cleanupCount_eq
  , `Effect4.Machine.cleanupEventIds
  , `Effect4.Machine.cleanupEventIds.eq_1
  , `Effect4.Machine.cleanupEventIds_eq
  , `Effect4.Machine.cleanupState
  , `Effect4.Machine.cleanupState.eq_1
  , `Effect4.Machine.cleanupState_eq
  , `Effect4.Machine.ctorIdx
  , `Effect4.Machine.fiber
  , `Effect4.Machine.fiber_eq_find
  , `Effect4.Machine.fibers
  , `Effect4.Machine.finished_iff
  , `Effect4.Machine.interruptPending
  , `Effect4.Machine.interruptPending.eq_1
  , `Effect4.Machine.interruptPending_eq
  , `Effect4.Machine.mask
  , `Effect4.Machine.mask.eq_1
  , `Effect4.Machine.mask_eq
  , `Effect4.Machine.mk
  , `Effect4.Machine.mk.inj
  , `Effect4.Machine.mk.injEq
  , `Effect4.Machine.mk.noConfusion
  , `Effect4.Machine.mk.sizeOf_spec
  , `Effect4.Machine.noConfusion
  , `Effect4.Machine.noConfusionType
  , `Effect4.Machine.rec
  , `Effect4.Machine.recOn
  , `Effect4.Machine.terminal
  , `Effect4.Machine.terminal.eq_1
  , `Effect4.Machine.terminal_eq
  , `Effect4.Machine.trace
  , `Effect4.Machine.transition
  , `Effect4.Machine.transition.eq_1
  , `Effect4.Machine.transition_cleanupEventIds
  , `Effect4.Machine.transition_fiber_other
  , `Effect4.Machine.transition_fibers
  , `Effect4.Machine.transition_trace
  , `Effect4.Machine.wellFormedDecidable
  , `Effect4.Machine.wellFormedDecidable.match_1
  , `Effect4.Machine.wellFormedDecidable.match_3
  , `Effect4.Machine.wellFormedDecidable.match_5
  , `Effect4.Machine.wellFormedDecidable.match_7
  , `Effect4.ReplayResult
  , `Effect4.ReplayResult.casesOn
  , `Effect4.ReplayResult.ctorElim
  , `Effect4.ReplayResult.ctorElimType
  , `Effect4.ReplayResult.ctorIdx
  , `Effect4.ReplayResult.finished
  , `Effect4.ReplayResult.finished.elim
  , `Effect4.ReplayResult.finished.inj
  , `Effect4.ReplayResult.finished.injEq
  , `Effect4.ReplayResult.finished.noConfusion
  , `Effect4.ReplayResult.finished.sizeOf_spec
  , `Effect4.ReplayResult.frontier
  , `Effect4.ReplayResult.frontier.elim
  , `Effect4.ReplayResult.frontier.inj
  , `Effect4.ReplayResult.frontier.injEq
  , `Effect4.ReplayResult.frontier.noConfusion
  , `Effect4.ReplayResult.frontier.sizeOf_spec
  , `Effect4.ReplayResult.machine
  , `Effect4.ReplayResult.machine.eq_1
  , `Effect4.ReplayResult.machine.eq_2
  , `Effect4.ReplayResult.machine.eq_3
  , `Effect4.ReplayResult.machine.match_1
  , `Effect4.ReplayResult.machine_finished
  , `Effect4.ReplayResult.machine_frontier
  , `Effect4.ReplayResult.machine_refused
  , `Effect4.ReplayResult.noConfusion
  , `Effect4.ReplayResult.noConfusionType
  , `Effect4.ReplayResult.rec
  , `Effect4.ReplayResult.recOn
  , `Effect4.ReplayResult.refused
  , `Effect4.ReplayResult.refused.elim
  , `Effect4.ReplayResult.refused.inj
  , `Effect4.ReplayResult.refused.injEq
  , `Effect4.ReplayResult.refused.noConfusion
  , `Effect4.ReplayResult.refused.sizeOf_spec
  , `Effect4.Runs
  , `Effect4.SchedulerDecision
  , `Effect4.SchedulerDecision.casesOn
  , `Effect4.SchedulerDecision.cases_receipt
  , `Effect4.SchedulerDecision.cleanup
  , `Effect4.SchedulerDecision.cleanup.elim
  , `Effect4.SchedulerDecision.cleanup.inj
  , `Effect4.SchedulerDecision.cleanup.injEq
  , `Effect4.SchedulerDecision.cleanup.noConfusion
  , `Effect4.SchedulerDecision.cleanup.sizeOf_spec
  , `Effect4.SchedulerDecision.complete
  , `Effect4.SchedulerDecision.complete.elim
  , `Effect4.SchedulerDecision.complete.inj
  , `Effect4.SchedulerDecision.complete.injEq
  , `Effect4.SchedulerDecision.complete.noConfusion
  , `Effect4.SchedulerDecision.complete.sizeOf_spec
  , `Effect4.SchedulerDecision.ctorElim
  , `Effect4.SchedulerDecision.ctorElimType
  , `Effect4.SchedulerDecision.ctorIdx
  , `Effect4.SchedulerDecision.enterMask
  , `Effect4.SchedulerDecision.enterMask.elim
  , `Effect4.SchedulerDecision.enterMask.inj
  , `Effect4.SchedulerDecision.enterMask.injEq
  , `Effect4.SchedulerDecision.enterMask.noConfusion
  , `Effect4.SchedulerDecision.enterMask.sizeOf_spec
  , `Effect4.SchedulerDecision.exitMask
  , `Effect4.SchedulerDecision.exitMask.elim
  , `Effect4.SchedulerDecision.exitMask.inj
  , `Effect4.SchedulerDecision.exitMask.injEq
  , `Effect4.SchedulerDecision.exitMask.noConfusion
  , `Effect4.SchedulerDecision.exitMask.sizeOf_spec
  , `Effect4.SchedulerDecision.join
  , `Effect4.SchedulerDecision.join.elim
  , `Effect4.SchedulerDecision.join.inj
  , `Effect4.SchedulerDecision.join.injEq
  , `Effect4.SchedulerDecision.join.noConfusion
  , `Effect4.SchedulerDecision.join.sizeOf_spec
  , `Effect4.SchedulerDecision.noConfusion
  , `Effect4.SchedulerDecision.noConfusionType
  , `Effect4.SchedulerDecision.rec
  , `Effect4.SchedulerDecision.recOn
  , `Effect4.SchedulerDecision.requestInterrupt
  , `Effect4.SchedulerDecision.requestInterrupt.elim
  , `Effect4.SchedulerDecision.requestInterrupt.inj
  , `Effect4.SchedulerDecision.requestInterrupt.injEq
  , `Effect4.SchedulerDecision.requestInterrupt.noConfusion
  , `Effect4.SchedulerDecision.requestInterrupt.sizeOf_spec
  , `Effect4.SchedulerDecision.schedule
  , `Effect4.SchedulerDecision.schedule.elim
  , `Effect4.SchedulerDecision.schedule.inj
  , `Effect4.SchedulerDecision.schedule.injEq
  , `Effect4.SchedulerDecision.schedule.noConfusion
  , `Effect4.SchedulerDecision.schedule.sizeOf_spec
  , `Effect4.SchedulerRefusal
  , `Effect4.SchedulerRefusal.casesOn
  , `Effect4.SchedulerRefusal.cases_receipt
  , `Effect4.SchedulerRefusal.ctorElim
  , `Effect4.SchedulerRefusal.ctorElimType
  , `Effect4.SchedulerRefusal.ctorIdx
  , `Effect4.SchedulerRefusal.invalidLifecycle
  , `Effect4.SchedulerRefusal.invalidLifecycle.elim
  , `Effect4.SchedulerRefusal.invalidLifecycle.inj
  , `Effect4.SchedulerRefusal.invalidLifecycle.injEq
  , `Effect4.SchedulerRefusal.invalidLifecycle.noConfusion
  , `Effect4.SchedulerRefusal.invalidLifecycle.sizeOf_spec
  , `Effect4.SchedulerRefusal.noConfusion
  , `Effect4.SchedulerRefusal.noConfusionType
  , `Effect4.SchedulerRefusal.rec
  , `Effect4.SchedulerRefusal.recOn
  , `Effect4.SchedulerRefusal.unknownFiber
  , `Effect4.SchedulerRefusal.unknownFiber.elim
  , `Effect4.SchedulerRefusal.unknownFiber.inj
  , `Effect4.SchedulerRefusal.unknownFiber.injEq
  , `Effect4.SchedulerRefusal.unknownFiber.noConfusion
  , `Effect4.SchedulerRefusal.unknownFiber.sizeOf_spec
  , `Effect4.Step
  , `Effect4.StepResult
  , `Effect4.StepResult.advanced
  , `Effect4.StepResult.advanced.elim
  , `Effect4.StepResult.advanced.inj
  , `Effect4.StepResult.advanced.injEq
  , `Effect4.StepResult.advanced.noConfusion
  , `Effect4.StepResult.advanced.sizeOf_spec
  , `Effect4.StepResult.casesOn
  , `Effect4.StepResult.ctorElim
  , `Effect4.StepResult.ctorElimType
  , `Effect4.StepResult.ctorIdx
  , `Effect4.StepResult.machine
  , `Effect4.StepResult.machine.eq_1
  , `Effect4.StepResult.machine.eq_2
  , `Effect4.StepResult.machine.match_1
  , `Effect4.StepResult.machine_advanced
  , `Effect4.StepResult.machine_refused
  , `Effect4.StepResult.noConfusion
  , `Effect4.StepResult.noConfusionType
  , `Effect4.StepResult.rec
  , `Effect4.StepResult.recOn
  , `Effect4.StepResult.refused
  , `Effect4.StepResult.refused.elim
  , `Effect4.StepResult.refused.inj
  , `Effect4.StepResult.refused.injEq
  , `Effect4.StepResult.refused.noConfusion
  , `Effect4.StepResult.refused.sizeOf_spec
  , `Effect4.Trace
  , `Effect4.activeDecision
  , `Effect4.cleanup_at_most_once
  , `Effect4.cleanup_count_monotone
  , `Effect4.cleanup_events_agree
  , `Effect4.cleanup_events_at_most_once
  , `Effect4.cleanup_exists
  , `Effect4.cleanup_preserves_terminal
  , `Effect4.cleanup_safe_on_finish
  , `Effect4.completion_exists
  , `Effect4.done_join_exists
  , `Effect4.double_join_agreement
  , `Effect4.enter_mask_exists
  , `Effect4.exists_representative_finished_run
  , `Effect4.finishedDecision
  , `Effect4.finite_replay_total
  , `Effect4.fixedTape_deterministic
  , `Effect4.instDecidableEqSchedulerRefusal
  , `Effect4.instDecidableEqSchedulerRefusal.decEq
  , `Effect4.instDecidableEqSchedulerRefusal.decEq.match_1
  , `Effect4.instReprSchedulerRefusal
  , `Effect4.instReprSchedulerRefusal.repr
  , `Effect4.instReprSchedulerRefusal.repr.match_1
  , `Effect4.interrupt_complete_order_distinct
  , `Effect4.invalid_completion_refuses
  , `Effect4.join_agreement
  , `Effect4.masked_interrupt_defers
  , `Effect4.masked_request_exists
  , `Effect4.pending_unmask_exists
  , `Effect4.representative_inputs_exist
  , `Effect4.runs_cons_iff
  , `Effect4.runs_nil_finished
  , `Effect4.runs_nil_frontier
  , `Effect4.runs_nil_iff
  , `Effect4.runs_preserves_wellFormed
  , `Effect4.stepEval
  , `Effect4.stepEval.eq_1
  , `Effect4.stepEval.eq_2
  , `Effect4.stepEval.eq_3
  , `Effect4.stepEval.eq_4
  , `Effect4.stepEval.eq_5
  , `Effect4.stepEval.eq_6
  , `Effect4.stepEval.eq_7
  , `Effect4.stepEval.match_1
  , `Effect4.stepEval.match_3
  , `Effect4.stepEval.match_5
  , `Effect4.stepEval_cleanup_invalid
  , `Effect4.stepEval_cleanup_missing
  , `Effect4.stepEval_cleanup_ready
  , `Effect4.stepEval_complete_invalid
  , `Effect4.stepEval_complete_missing
  , `Effect4.stepEval_complete_running
  , `Effect4.stepEval_enterMask
  , `Effect4.stepEval_enterMask_inactive
  , `Effect4.stepEval_enterMask_invalid
  , `Effect4.stepEval_enterMask_missing
  , `Effect4.stepEval_exitMask_clear
  , `Effect4.stepEval_exitMask_inactive
  , `Effect4.stepEval_exitMask_invalid
  , `Effect4.stepEval_exitMask_missing
  , `Effect4.stepEval_exitMask_pending
  , `Effect4.stepEval_interrupt_invalid
  , `Effect4.stepEval_interrupt_masked
  , `Effect4.stepEval_interrupt_missing_requester
  , `Effect4.stepEval_interrupt_missing_target
  , `Effect4.stepEval_interrupt_unmasked
  , `Effect4.stepEval_join_done
  , `Effect4.stepEval_join_done_invalid
  , `Effect4.stepEval_join_done_missing_terminal
  , `Effect4.stepEval_join_invalid
  , `Effect4.stepEval_join_missing_target
  , `Effect4.stepEval_join_missing_waiter
  , `Effect4.stepEval_join_self_invalid
  , `Effect4.stepEval_join_waiting
  , `Effect4.stepEval_schedule_invalid
  , `Effect4.stepEval_schedule_missing
  , `Effect4.stepEval_schedule_runnable
  , `Effect4.step_deterministic
  , `Effect4.step_iff
  , `Effect4.step_preserves_wellFormed
  , `Effect4.step_total
  , `Effect4.unknown_schedule_refuses
  , `Effect4.unmask_delivers_pending
  , `Effect4.unmask_without_pending_exists
  , `Effect4.unmasked_interrupt_delivers
  , `Effect4.unmasked_request_exists
  , `Effect4.waiting_join_exists
  ]

private def authoredApiDeclarations :=
  [ (`Effect4.FiberStatus, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.InterruptMask, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-INTERRUPT-MASK/CONSTRUCTION")
  , (`Effect4.CleanupState, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-CLEANUP-STATE/CONSTRUCTION")
  , (`Effect4.SchedulerRefusal, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REFUSAL/SEMANTICS")
  , (`Effect4.FiberId, `Effect4.Concurrency.Fiber, "FIBER-LEAF-ID/IDENTITY")
  , (`Effect4.FiberId.mk, `Effect4.Concurrency.Fiber, "FIBER-LEAF-ID/IDENTITY")
  , (`Effect4.FiberId.value, `Effect4.Concurrency.Fiber, "FIBER-LEAF-ID/IDENTITY")
  , (`Effect4.FiberStatus.runnable, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.running, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.waiting, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.finalizing, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.done, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.Active, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.active_iff, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.activeDecidable, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.InterruptMask.unmasked, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-INTERRUPT-MASK/CONSTRUCTION")
  , (`Effect4.InterruptMask.masked, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-INTERRUPT-MASK/CONSTRUCTION")
  , (`Effect4.CleanupState.notStarted, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-CLEANUP-STATE/CONSTRUCTION")
  , (`Effect4.CleanupState.pending, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-CLEANUP-STATE/CONSTRUCTION")
  , (`Effect4.CleanupState.done, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-CLEANUP-STATE/CONSTRUCTION")
  , (`Effect4.SchedulerRefusal.unknownFiber, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REFUSAL/SEMANTICS")
  , (`Effect4.SchedulerRefusal.invalidLifecycle, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REFUSAL/SEMANTICS")
  , (`Effect4.InterruptBoundary, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-BOUNDARY/SEMANTICS")
  , (`Effect4.InterruptBoundary.mk, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-BOUNDARY/SEMANTICS")
  , (`Effect4.InterruptBoundary.interrupted, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-BOUNDARY/SEMANTICS")
  , (`Effect4.FiberState, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.mk, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.id, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.status, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.terminal, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.mask, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.interruptPending, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.cleanup, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.FiberState.cleanupCount, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATE/SEMANTICS")
  , (`Effect4.SchedulerDecision, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.schedule, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.join, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.requestInterrupt, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.enterMask, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.exitMask, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.complete, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.SchedulerDecision.cleanup, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.DecisionTape, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-TAPE/SEMANTICS")
  , (`Effect4.Event, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.scheduled, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.joinWaiting, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.joinObserved, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.interruptRequested, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.interruptDeferred, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.interruptDelivered, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.maskEntered, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.maskExited, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.completed, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.cleanupFinished, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.cleanupId?, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Event.cleanupId_eq_some, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Trace, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-TRACE/SEMANTICS")
  , (`Effect4.Machine, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-MACHINE/SEMANTICS")
  , (`Effect4.Machine.mk, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-MACHINE/SEMANTICS")
  , (`Effect4.Machine.fibers, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-MACHINE/SEMANTICS")
  , (`Effect4.Machine.trace, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-MACHINE/SEMANTICS")
  , (`Effect4.Machine.fiber, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.terminal, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.mask, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.interruptPending, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupState, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupCount, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupEventIds, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.fiber_eq_find, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.terminal_eq, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.mask_eq, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.interruptPending_eq, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupState_eq, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupCount_eq, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupEventIds_eq, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_fibers, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_trace, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_cleanupEventIds, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_fiber_other, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.WellFormed, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.mk, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.idsUnique, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.cleanupBounded, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.cleanupEventsUnique, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.cleanupEventsClosed, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.cleanupEventAgreement, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.activeCleanup, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.finalizingCleanup, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.doneCleanup, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.pendingActive, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.WellFormed.waitingClosed, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.wellFormedDecidable, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , (`Effect4.Machine.Finished, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.finished_iff, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.StepResult, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.StepResult.advanced, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.StepResult.refused, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.StepResult.machine, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.StepResult.machine_advanced, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.StepResult.machine_refused, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.finished, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.refused, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.frontier, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine_finished, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine_refused, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine_frontier, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.Step, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Runs, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.step_iff, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.FiberStatus.cases_receipt, `Effect4.Concurrency.Fiber, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.InterruptMask.cases_receipt, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-INTERRUPT-MASK/CONSTRUCTION")
  , (`Effect4.CleanupState.cases_receipt, `Effect4.Concurrency.Interrupt, "FIBER-LEAF-CLEANUP-STATE/CONSTRUCTION")
  , (`Effect4.SchedulerRefusal.cases_receipt, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-REFUSAL/SEMANTICS")
  , (`Effect4.SchedulerDecision.cases_receipt, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.Event.cases_receipt, `Effect4.Concurrency.Scheduler, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.step_deterministic, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.fixedTape_deterministic, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.step_preserves_wellFormed, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.runs_preserves_wellFormed, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.finite_replay_total, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.step_total, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_schedule_missing, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_schedule_runnable, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_schedule_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_missing_waiter, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_missing_target, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_done, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_done_missing_terminal, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_waiting, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_done_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_self_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_missing_requester, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_missing_target, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_masked, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_unmasked, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask_missing, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask_inactive, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_missing, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_pending, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_clear, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_inactive, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_complete_missing, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_complete_running, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_complete_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_cleanup_missing, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_cleanup_ready, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_cleanup_invalid, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_nil_iff, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_cons_iff, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.done_join_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.waiting_join_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.masked_request_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.unmasked_request_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.enter_mask_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.pending_unmask_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.unmask_without_pending_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.completion_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.cleanup_exists, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.unknown_schedule_refuses, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.invalid_completion_refuses, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.representative_inputs_exist, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_nil_finished, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_nil_frontier, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.exists_representative_finished_run, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.join_agreement, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.double_join_agreement, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.unmasked_interrupt_delivers, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.masked_interrupt_defers, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.unmask_delivers_pending, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_count_monotone, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_at_most_once, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_events_at_most_once, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_events_agree, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_preserves_terminal, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_safe_on_finish, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.interrupt_complete_order_distinct, `Effect4.Concurrency.Scheduler, "FIBER-PG-REPRESENTATIVE/COUNTEREXAMPLES")
  ]

private def theoremReceipts :=
  [ (`Effect4.InterruptMask.cases_receipt, "FIBER-LEAF-INTERRUPT-MASK/CONSTRUCTION")
  , (`Effect4.CleanupState.cases_receipt, "FIBER-LEAF-CLEANUP-STATE/CONSTRUCTION")
  , (`Effect4.FiberStatus.active_iff, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.FiberStatus.cases_receipt, "FIBER-LEAF-STATUS/CONSTRUCTION")
  , (`Effect4.Event.cleanupId_eq_some, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.Machine.fiber_eq_find, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.terminal_eq, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.mask_eq, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.interruptPending_eq, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupState_eq, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupCount_eq, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.cleanupEventIds_eq, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_fibers, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_trace, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_cleanupEventIds, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.transition_fiber_other, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.Machine.finished_iff, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.SchedulerRefusal.cases_receipt, "FIBER-LEAF-REFUSAL/SEMANTICS")
  , (`Effect4.SchedulerDecision.cases_receipt, "FIBER-LEAF-DECISION/SEMANTICS")
  , (`Effect4.Event.cases_receipt, "FIBER-LEAF-EVENT/SEMANTICS")
  , (`Effect4.StepResult.machine_advanced, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.StepResult.machine_refused, "FIBER-LEAF-STEP-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine_finished, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine_refused, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.ReplayResult.machine_frontier, "FIBER-LEAF-REPLAY-RESULT/SEMANTICS")
  , (`Effect4.step_iff, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_schedule_missing, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_schedule_runnable, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_schedule_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_missing_waiter, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_missing_target, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_done, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_done_missing_terminal, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_waiting, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_done_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_join_self_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_missing_requester, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_missing_target, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_masked, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_unmasked, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_interrupt_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask_missing, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_enterMask_inactive, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_missing, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_pending, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_clear, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_exitMask_inactive, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_complete_missing, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_complete_running, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_complete_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_cleanup_missing, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_cleanup_ready, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.stepEval_cleanup_invalid, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.step_deterministic, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.step_preserves_wellFormed, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.runs_nil_iff, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_cons_iff, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.fixedTape_deterministic, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.finite_replay_total, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.step_total, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_preserves_wellFormed, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.done_join_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.waiting_join_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.masked_request_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.unmasked_request_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.enter_mask_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.pending_unmask_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.unmask_without_pending_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.completion_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.cleanup_exists, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.unknown_schedule_refuses, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.invalid_completion_refuses, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_nil_finished, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.runs_nil_frontier, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.join_agreement, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.double_join_agreement, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.unmasked_interrupt_delivers, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.masked_interrupt_defers, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.unmask_delivers_pending, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_preserves_terminal, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_at_most_once, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_events_at_most_once, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_events_agree, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_count_monotone, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.cleanup_safe_on_finish, "FIBER-PG-REPRESENTATIVE/LAWS")
  , (`Effect4.representative_inputs_exist, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.exists_representative_finished_run, "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , (`Effect4.interrupt_complete_order_distinct, "FIBER-PG-REPRESENTATIVE/COUNTEREXAMPLES")
  ]

private def axiomReceipts :=
  [ (`Effect4.InterruptMask.cases_receipt, "propext")
  , (`Effect4.CleanupState.cases_receipt, "propext")
  , (`Effect4.FiberStatus.active_iff, "propext,Quot.sound")
  , (`Effect4.FiberStatus.cases_receipt, "propext,Quot.sound")
  , (`Effect4.Event.cleanupId_eq_some, "propext")
  , (`Effect4.Machine.fiber_eq_find, "none")
  , (`Effect4.Machine.terminal_eq, "none")
  , (`Effect4.Machine.mask_eq, "none")
  , (`Effect4.Machine.interruptPending_eq, "none")
  , (`Effect4.Machine.cleanupState_eq, "none")
  , (`Effect4.Machine.cleanupCount_eq, "none")
  , (`Effect4.Machine.cleanupEventIds_eq, "propext")
  , (`Effect4.Machine.transition_fibers, "none")
  , (`Effect4.Machine.transition_trace, "none")
  , (`Effect4.Machine.transition_cleanupEventIds, "propext")
  , (`Effect4.Machine.transition_fiber_other, "propext")
  , (`Effect4.Machine.finished_iff, "none")
  , (`Effect4.SchedulerRefusal.cases_receipt, "propext,Quot.sound")
  , (`Effect4.SchedulerDecision.cases_receipt, "propext,Quot.sound")
  , (`Effect4.Event.cases_receipt, "propext,Quot.sound")
  , (`Effect4.StepResult.machine_advanced, "none")
  , (`Effect4.StepResult.machine_refused, "none")
  , (`Effect4.ReplayResult.machine_finished, "none")
  , (`Effect4.ReplayResult.machine_refused, "none")
  , (`Effect4.ReplayResult.machine_frontier, "none")
  , (`Effect4.step_iff, "none")
  , (`Effect4.stepEval_schedule_missing, "propext")
  , (`Effect4.stepEval_schedule_runnable, "propext")
  , (`Effect4.stepEval_schedule_invalid, "propext")
  , (`Effect4.stepEval_join_missing_waiter, "propext")
  , (`Effect4.stepEval_join_missing_target, "propext")
  , (`Effect4.stepEval_join_done, "propext")
  , (`Effect4.stepEval_join_done_missing_terminal, "propext")
  , (`Effect4.stepEval_join_waiting, "propext")
  , (`Effect4.stepEval_join_invalid, "propext")
  , (`Effect4.stepEval_join_done_invalid, "propext")
  , (`Effect4.stepEval_join_self_invalid, "propext")
  , (`Effect4.stepEval_interrupt_missing_requester, "propext")
  , (`Effect4.stepEval_interrupt_missing_target, "propext")
  , (`Effect4.stepEval_interrupt_masked, "propext")
  , (`Effect4.stepEval_interrupt_unmasked, "propext")
  , (`Effect4.stepEval_interrupt_invalid, "propext")
  , (`Effect4.stepEval_enterMask_missing, "propext")
  , (`Effect4.stepEval_enterMask, "propext")
  , (`Effect4.stepEval_enterMask_invalid, "propext")
  , (`Effect4.stepEval_enterMask_inactive, "propext")
  , (`Effect4.stepEval_exitMask_missing, "propext")
  , (`Effect4.stepEval_exitMask_pending, "propext")
  , (`Effect4.stepEval_exitMask_clear, "propext")
  , (`Effect4.stepEval_exitMask_invalid, "propext")
  , (`Effect4.stepEval_exitMask_inactive, "propext")
  , (`Effect4.stepEval_complete_missing, "propext")
  , (`Effect4.stepEval_complete_running, "propext")
  , (`Effect4.stepEval_complete_invalid, "propext")
  , (`Effect4.stepEval_cleanup_missing, "propext")
  , (`Effect4.stepEval_cleanup_ready, "propext")
  , (`Effect4.stepEval_cleanup_invalid, "propext")
  , (`Effect4.step_deterministic, "none")
  , (`Effect4.step_preserves_wellFormed, "propext,Quot.sound")
  , (`Effect4.runs_nil_iff, "propext,Quot.sound")
  , (`Effect4.runs_cons_iff, "propext,Quot.sound")
  , (`Effect4.fixedTape_deterministic, "propext,Quot.sound")
  , (`Effect4.finite_replay_total, "propext,Quot.sound")
  , (`Effect4.step_total, "propext")
  , (`Effect4.runs_preserves_wellFormed, "propext,Quot.sound")
  , (`Effect4.done_join_exists, "propext")
  , (`Effect4.waiting_join_exists, "propext")
  , (`Effect4.masked_request_exists, "propext")
  , (`Effect4.unmasked_request_exists, "propext")
  , (`Effect4.enter_mask_exists, "propext")
  , (`Effect4.pending_unmask_exists, "propext")
  , (`Effect4.unmask_without_pending_exists, "propext")
  , (`Effect4.completion_exists, "propext")
  , (`Effect4.cleanup_exists, "propext")
  , (`Effect4.unknown_schedule_refuses, "propext")
  , (`Effect4.invalid_completion_refuses, "propext")
  , (`Effect4.runs_nil_finished, "propext,Quot.sound")
  , (`Effect4.runs_nil_frontier, "propext,Quot.sound")
  , (`Effect4.join_agreement, "propext")
  , (`Effect4.double_join_agreement, "propext")
  , (`Effect4.unmasked_interrupt_delivers, "propext")
  , (`Effect4.masked_interrupt_defers, "propext")
  , (`Effect4.unmask_delivers_pending, "propext")
  , (`Effect4.cleanup_preserves_terminal, "propext")
  , (`Effect4.cleanup_at_most_once, "propext,Quot.sound")
  , (`Effect4.cleanup_events_at_most_once, "propext,Quot.sound")
  , (`Effect4.cleanup_events_agree, "propext,Quot.sound")
  , (`Effect4.cleanup_count_monotone, "propext,Quot.sound")
  , (`Effect4.cleanup_safe_on_finish, "propext,Quot.sound")
  , (`Effect4.representative_inputs_exist, "propext,Quot.sound")
  , (`Effect4.exists_representative_finished_run, "propext,Quot.sound")
  , (`Effect4.interrupt_complete_order_distinct, "propext,Quot.sound")
  ]

private def typeRows :=
  [ ("E4-TYPE-FIBER-ID", `Effect4.FiberId, `Effect4.Concurrency.Fiber, "canonical", "FIBER-LEAF-ID")
  , ("E4-TYPE-FIBER-STATUS", `Effect4.FiberStatus, `Effect4.Concurrency.Fiber, "canonical", "FIBER-LEAF-STATUS")
  , ("E4-TYPE-FIBER-STATE", `Effect4.FiberState, `Effect4.Concurrency.Fiber, "canonical", "FIBER-LEAF-STATE")
  , ("E4-TYPE-INTERRUPT-MASK", `Effect4.InterruptMask, `Effect4.Concurrency.Interrupt, "canonical", "FIBER-LEAF-INTERRUPT-MASK")
  , ("E4-TYPE-CLEANUP-STATE", `Effect4.CleanupState, `Effect4.Concurrency.Interrupt, "canonical", "FIBER-LEAF-CLEANUP-STATE")
  , ("E4-TYPE-INTERRUPT-BOUNDARY", `Effect4.InterruptBoundary, `Effect4.Concurrency.Interrupt, "canonical-boundary", "FIBER-LEAF-BOUNDARY")
  , ("E4-TYPE-SCHEDULER-REFUSAL", `Effect4.SchedulerRefusal, `Effect4.Concurrency.Scheduler, "canonical-label", "FIBER-LEAF-REFUSAL")
  , ("E4-TYPE-SCHEDULER-DECISION", `Effect4.SchedulerDecision, `Effect4.Concurrency.Scheduler, "canonical", "FIBER-LEAF-DECISION")
  , ("E4-TYPE-DECISION-TAPE", `Effect4.DecisionTape, `Effect4.Concurrency.Scheduler, "derived-list-alias", "FIBER-LEAF-TAPE")
  , ("E4-TYPE-EVENT", `Effect4.Event, `Effect4.Concurrency.Scheduler, "canonical", "FIBER-LEAF-EVENT")
  , ("E4-TYPE-TRACE", `Effect4.Trace, `Effect4.Concurrency.Scheduler, "derived-list-alias", "FIBER-LEAF-TRACE")
  , ("E4-TYPE-MACHINE", `Effect4.Machine, `Effect4.Concurrency.Scheduler, "canonical", "FIBER-LEAF-MACHINE")
  , ("E4-TYPE-MACHINE-WELLFORMED", `Effect4.Machine.WellFormed, `Effect4.Concurrency.Scheduler, "canonical-admission", "FIBER-PG-REPRESENTATIVE/CONSTRUCTION")
  , ("E4-TYPE-MACHINE-FINISHED", `Effect4.Machine.Finished, `Effect4.Concurrency.Scheduler, "canonical-predicate", "FIBER-PG-REPRESENTATIVE/SEMANTICS")
  , ("E4-TYPE-STEP-RESULT", `Effect4.StepResult, `Effect4.Concurrency.Scheduler, "derived-envelope", "FIBER-LEAF-STEP-RESULT")
  , ("E4-TYPE-REPLAY-RESULT", `Effect4.ReplayResult, `Effect4.Concurrency.Scheduler, "canonical-envelope", "FIBER-LEAF-REPLAY-RESULT")
  ]

private def leafReceipts :=
  [ ("FIBER-LEAF-ID", `Effect4.FiberId, "FIBER-PG-REPRESENTATIVE/IDENTITY", "signature-field-decidableeq-repr")
  , ("FIBER-LEAF-STATUS", `Effect4.FiberStatus, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION", "five-constructors-active-cases-decidableeq-repr")
  , ("FIBER-LEAF-STATE", `Effect4.FiberState, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "seven-fields")
  , ("FIBER-LEAF-INTERRUPT-MASK", `Effect4.InterruptMask, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION", "two-constructors-cases-decidableeq-repr")
  , ("FIBER-LEAF-CLEANUP-STATE", `Effect4.CleanupState, "FIBER-PG-REPRESENTATIVE/CONSTRUCTION", "three-constructors-cases-decidableeq-repr")
  , ("FIBER-LEAF-BOUNDARY", `Effect4.InterruptBoundary, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "one-field-external-terminal")
  , ("FIBER-LEAF-REFUSAL", `Effect4.SchedulerRefusal, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "two-labels-cases-decidableeq-repr")
  , ("FIBER-LEAF-DECISION", `Effect4.SchedulerDecision, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "seven-explicit-decisions-cases")
  , ("FIBER-LEAF-TAPE", `Effect4.DecisionTape, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "list-alias")
  , ("FIBER-LEAF-EVENT", `Effect4.Event, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "ten-events-cases-cleanup-projection")
  , ("FIBER-LEAF-TRACE", `Effect4.Trace, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "list-alias")
  , ("FIBER-LEAF-MACHINE", `Effect4.Machine, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "fibers-trace-projections")
  , ("FIBER-LEAF-STEP-RESULT", `Effect4.StepResult, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "two-arms-machine-projection")
  , ("FIBER-LEAF-REPLAY-RESULT", `Effect4.ReplayResult, "FIBER-PG-REPRESENTATIVE/SEMANTICS", "finished-refused-frontier-machine-projection")
  ]

private def forbiddenDuplicateDeclarations :=
  [ (`Effect4.FiberTerminal, "duplicate-terminal-carrier")
  , (`Effect4.Terminal, "duplicate-terminal-carrier")
  , (`Effect4.Frontier, "duplicate-frontier-carrier")
  , (`Effect4.FiberFrontier, "duplicate-frontier-carrier")
  , (`Effect4.SchedulerFrontier, "duplicate-frontier-carrier")
  , (`Effect4.CheckedMachine, "duplicate-checked-machine-carrier")
  , (`Effect4.Machine.Checked, "duplicate-checked-machine-carrier")
  , (`Effect4.CleanupTrace, "duplicate-trace-carrier")
  , (`Effect4.DecisionTrace, "duplicate-tape-carrier")
  , (`Effect4.UntapedStep, "unrecorded-choice-semantics")
  , (`Effect4.UntapedRuns, "unrecorded-choice-semantics")
  , (`Effect4.FiberHandler, "duplicate-runtime-carrier")
  ]

private def graphEdges :=
  [ ("IDENTITY", "FIBER-L0-ID", "required")
  , ("CONSTRUCTION", "FIBER-L0-PASSIVE-ALPHABETS+FIBER-L1-ADMISSION", "required")
  , ("SEMANTICS", "FIBER-L1-STATE+FIBER-L1-DECISION-TAPE+FIBER-L2-STEP+FIBER-L3-RUNS", "required")
  , ("LAWS", "FIBER-L4-DETERMINISM+FIBER-L4-JOIN+FIBER-L4-INTERRUPT+FIBER-L4-CLEANUP", "required")
  , ("REPRESENTATION", "no-serialization-normalization-roundtrip-claim", "not-applicable")
  , ("COUNTEREXAMPLES", "FIBER-L5-COUNTEREXAMPLES", "required")
  , ("BRIDGES", "no-embedding-compatibility-bridge-claim", "not-applicable")
  , ("TARGETS", "FIBER-L6-HOST-EVIDENCE-LATER", "not-applicable")
  , ("TRUST", "FIBER-AXIOM-RECEIPTS", "required")
  , ("COVERAGE", "FIBER-EXACT-CENSUS-AND-API-JOIN", "required")
  ]

private def checkTheoremReceipts : CommandElabM Unit := do
  checkUniqueNames "theorem receipt" (theoremReceipts.map Prod.fst)
  let environment ← getEnv
  for (name, _) in theoremReceipts do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | some _ => failJoin m!"contracted theorem {name} is not a theorem declaration"
    | none => failJoin m!"missing contracted theorem {name}"

private def canonicalAxiomText (name : Name) : CommandElabM String := do
  let actual := (← collectAxioms name).toList
  let unknown := actual.filter fun axiomName =>
    axiomName != `propext && axiomName != `Quot.sound
  unless unknown.isEmpty do
    failJoin m!"unexpected kernel axioms for {name}: {unknown}"
  let hasPropext := actual.contains `propext
  let hasQuotSound := actual.contains `Quot.sound
  pure <| match hasPropext, hasQuotSound with
    | false, false => "none"
    | true, false => "propext"
    | false, true => "Quot.sound"
    | true, true => "propext,Quot.sound"

private def checkAxiomReceipts : CommandElabM Unit := do
  let theoremNames := theoremReceipts.map Prod.fst
  let axiomNames := axiomReceipts.map Prod.fst
  checkUniqueNames "axiom receipt" axiomNames
  unless sameNameSet theoremNames axiomNames do
    failJoin m!"theorem and axiom receipt names differ"
  for (name, expected) in axiomReceipts do
    unless expected == "none" || expected == "propext" ||
        expected == "Quot.sound" || expected == "propext,Quot.sound" do
      failJoin m!"unexpected Fiber axiom ceiling spelling: {expected}"
    let actual ← canonicalAxiomText name
    unless actual == expected do
      failJoin m!"axiom receipt for {name}: expected {expected}, found {actual}"

private def checkAuthoredApi : CommandElabM Unit := do
  let apiNames := authoredApiDeclarations.map fun row => row.1
  checkUniqueNames "authored API" apiNames
  unless apiNames.length == 185 do
    failJoin m!"authored API count drifted: {apiNames.length}"
  unless (theoremReceipts.map Prod.fst).all apiNames.contains do
    failJoin m!"a theorem receipt is missing from the authored API"
  for (name, owner, _) in authoredApiDeclarations do
    checkOwners owner [name]

private def checkForbiddenDuplicates : CommandElabM Unit := do
  checkUniqueNames "forbidden duplicate declaration"
    (forbiddenDuplicateDeclarations.map fun row => row.1)
  let environment ← getEnv
  for (name, defect) in forbiddenDuplicateDeclarations do
    if environment.contains name then
      failJoin m!"forbidden {defect} declaration is present: {name}"

private def checkClassificationRows : CommandElabM Unit := do
  checkUniqueStrings "type row" (typeRows.map fun row => row.1)
  checkUniqueNames "classified type" (typeRows.map fun row => row.2.1)
  for (_, name, owner, _, _) in typeRows do
    checkOwners owner [name]
  checkUniqueStrings "passive leaf receipt" (leafReceipts.map fun row => row.1)
  checkUniqueNames "passive leaf type" (leafReceipts.map fun row => row.2.1)
  let environment ← getEnv
  for (_, name, _, _) in leafReceipts do
    unless environment.contains name do
      failJoin m!"missing passive leaf declaration {name}"

private def checkGraphRows : CommandElabM Unit := do
  checkUniqueStrings "proof graph edge" (graphEdges.map fun row => row.1)
  unless graphEdges.length == 10 do
    failJoin m!"proof graph edge count drifted: {graphEdges.length}"
  for (edge, _, declaredState) in graphEdges do
    unless declaredState == "required" || declaredState == "not-applicable" do
      failJoin m!"invalid state for proof graph edge {edge}: {declaredState}"

private def checkFiberAssurance : CommandElabM Unit := do
  checkExactModuleSurface `Effect4.Concurrency.Interrupt expectedInterruptOwned
  checkExactModuleSurface `Effect4.Concurrency.Fiber expectedFiberOwned
  checkExactModuleSurface `Effect4.Concurrency.Scheduler expectedSchedulerOwned
  checkAuthoredApi
  checkTheoremReceipts
  checkAxiomReceipts
  checkClassificationRows
  checkGraphRows
  checkForbiddenDuplicates

private def emitFiberAssurance : CommandElabM Unit := do
  checkFiberAssurance
  for (owner, names) in
      [(`Effect4.Concurrency.Interrupt, expectedInterruptOwned),
       (`Effect4.Concurrency.Fiber, expectedFiberOwned),
       (`Effect4.Concurrency.Scheduler, expectedSchedulerOwned)] do
    for name in names do
      liftIO <| IO.println s!"E4FIBER\towned-declaration\t{name}\t{owner}\tFIBER-PG-REPRESENTATIVE"
  for (name, owner, route) in authoredApiDeclarations do
    liftIO <| IO.println s!"E4FIBER\tapi\t{name}\t{owner}\t{route}"
  for (name, route) in theoremReceipts do
    liftIO <| IO.println s!"E4FIBER\ttheorem\t{name}\t{route}"
  for (name, expected) in axiomReceipts do
    let actual ← canonicalAxiomText name
    unless actual == expected do
      failJoin m!"axiom receipt for {name}: expected {expected}, found {actual}"
    liftIO <| IO.println s!"E4FIBER\taxiom\t{name}\t{actual}\tFIBER-AXIOM-RECEIPT"
  for (id, name, owner, relationship, route) in typeRows do
    liftIO <| IO.println s!"E4FIBER\ttype\t{id}\t{name}\t{owner}\t{relationship}\t{route}"
  for (id, name, parent, evidence) in leafReceipts do
    liftIO <| IO.println s!"E4FIBER\tleaf-receipt\t{id}\t{name}\t{parent}\t{evidence}"
  for (name, defect) in forbiddenDuplicateDeclarations do
    liftIO <| IO.println s!"E4FIBER\tabsent\t{name}\t{defect}\tchecked"
  for (edge, node, declaredState) in graphEdges do
    liftIO <| IO.println s!"E4FIBER\tgraph-edge\tFIBER-PG-REPRESENTATIVE/{edge}\t{node}\t{declaredState}"

syntax (name := effect4CheckFiberAssurance)
  "#effect4_check_fiber_assurance" : command

syntax (name := effect4EmitFiberAssurance)
  "#effect4_emit_fiber_assurance" : command

syntax (name := effect4CheckExactCurrentFiberModuleSurface)
  "#effect4_check_exact_current_fiber_module_surface " "[" ident,* "]" : command

syntax (name := effect4CheckFiberDeclarationOwners)
  "#effect4_check_fiber_declaration_owners " ident "[" ident,* "]" : command

elab_rules : command
  | `(#effect4_check_fiber_assurance) => checkFiberAssurance

elab_rules : command
  | `(#effect4_emit_fiber_assurance) => emitFiberAssurance

elab_rules : command
  | `(#effect4_check_exact_current_fiber_module_surface [$names:ident,*]) => do
      let environment ← getEnv
      checkExactModuleSurface environment.mainModule
        (names.getElems.map Syntax.getId).toList

elab_rules : command
  | `(#effect4_check_fiber_declaration_owners $owner:ident [$names:ident,*]) =>
      checkOwners owner.getId (names.getElems.map Syntax.getId).toList

#effect4_check_fiber_assurance
#effect4_emit_fiber_assurance

/-! ## Independent supervision controller assurance

The frozen declaration battery, 27 dispositions, and 19 exact shapes are
owned by the breaker packet at 5568f00. This join derives local receipts;
BRIDGES, TARGETS, and TRUST stay required-open: local axiom receipts do not
bind a fresh repository trust-gate result to this generated graph.
The original representative lists and checks above are unchanged.
-/

private def supervisionOwned : List Name :=
  [ `Effect4.Scope.finalizerKeys.eq_1
  , `Effect4.Scope.finalizers.eq_1
  , `Effect4.Scope.tableRemove.eq_1
  , `Effect4.ScopeState.entries.eq_1
  , `Effect4.ScopeState.entries.eq_2
  , `Effect4.ScopeState.entries.eq_3
  , `Effect4.ScopeState.entries.eq_4
  , `Effect4.ScopeState.entries.eq_5
  , `Effect4.Supervision.Fiber
  , `Effect4.Supervision.Fiber.Valid
  , `Effect4.Supervision.Fiber.Valid.eq_1
  , `Effect4.Supervision.Fiber.addChild
  , `Effect4.Supervision.Fiber.addChild_eq
  , `Effect4.Supervision.Fiber.addChild_nodup
  , `Effect4.Supervision.Fiber.cancel
  , `Effect4.Supervision.Fiber.cancel.eq_1
  , `Effect4.Supervision.Fiber.cancel_eq
  , `Effect4.Supervision.Fiber.cancel_membership
  , `Effect4.Supervision.Fiber.casesOn
  , `Effect4.Supervision.Fiber.children
  , `Effect4.Supervision.Fiber.context
  , `Effect4.Supervision.Fiber.core
  , `Effect4.Supervision.Fiber.ctorIdx
  , `Effect4.Supervision.Fiber.interrupted
  , `Effect4.Supervision.Fiber.mk
  , `Effect4.Supervision.Fiber.mk.inj
  , `Effect4.Supervision.Fiber.mk.injEq
  , `Effect4.Supervision.Fiber.mk.noConfusion
  , `Effect4.Supervision.Fiber.mk.sizeOf_spec
  , `Effect4.Supervision.Fiber.noConfusion
  , `Effect4.Supervision.Fiber.noConfusionType
  , `Effect4.Supervision.Fiber.observe
  , `Effect4.Supervision.Fiber.observe.eq_1
  , `Effect4.Supervision.Fiber.observe.match_1
  , `Effect4.Supervision.Fiber.observe_done
  , `Effect4.Supervision.Fiber.observe_duplicate
  , `Effect4.Supervision.Fiber.observe_invalid
  , `Effect4.Supervision.Fiber.observe_live
  , `Effect4.Supervision.Fiber.publish
  , `Effect4.Supervision.Fiber.publish.eq_1
  , `Effect4.Supervision.Fiber.publish_eq
  , `Effect4.Supervision.Fiber.publish_valid
  , `Effect4.Supervision.Fiber.published?
  , `Effect4.Supervision.Fiber.published?.eq_1
  , `Effect4.Supervision.Fiber.published_eq
  , `Effect4.Supervision.Fiber.published_iff
  , `Effect4.Supervision.Fiber.rec
  , `Effect4.Supervision.Fiber.recOn
  , `Effect4.Supervision.Fiber.recordInterrupt
  , `Effect4.Supervision.Fiber.recordInterrupt.eq_1
  , `Effect4.Supervision.Fiber.recordInterrupt.match_1
  , `Effect4.Supervision.Fiber.recordInterrupt_core
  , `Effect4.Supervision.Fiber.recordInterrupt_done
  , `Effect4.Supervision.Fiber.recordInterrupt_live
  , `Effect4.Supervision.Fiber.removeChild
  , `Effect4.Supervision.Fiber.removeChild.eq_1
  , `Effect4.Supervision.Fiber.removeChild_eq
  , `Effect4.Supervision.Fiber.removeChild_membership
  , `Effect4.Supervision.Fiber.subscriptions
  , `Effect4.Supervision.Fiber.toFiberState
  , `Effect4.Supervision.Fiber.toFiberState_eq
  , `Effect4.Supervision.Fiber.valid?
  , `Effect4.Supervision.Fiber.valid?.eq_1
  , `Effect4.Supervision.Fiber.valid?.match_1
  , `Effect4.Supervision.Fiber.valid?_iff
  , `Effect4.Supervision.Fiber.valid_iff
  , `Effect4.Supervision.ForkEvent
  , `Effect4.Supervision.ForkEvent.casesOn
  , `Effect4.Supervision.ForkEvent.ctorElim
  , `Effect4.Supervision.ForkEvent.ctorElimType
  , `Effect4.Supervision.ForkEvent.ctorIdx
  , `Effect4.Supervision.ForkEvent.evaluated
  , `Effect4.Supervision.ForkEvent.evaluated.elim
  , `Effect4.Supervision.ForkEvent.evaluated.inj
  , `Effect4.Supervision.ForkEvent.evaluated.injEq
  , `Effect4.Supervision.ForkEvent.evaluated.noConfusion
  , `Effect4.Supervision.ForkEvent.evaluated.sizeOf_spec
  , `Effect4.Supervision.ForkEvent.noConfusion
  , `Effect4.Supervision.ForkEvent.noConfusionType
  , `Effect4.Supervision.ForkEvent.rec
  , `Effect4.Supervision.ForkEvent.recOn
  , `Effect4.Supervision.ForkEvent.registered
  , `Effect4.Supervision.ForkEvent.registered.elim
  , `Effect4.Supervision.ForkEvent.registered.inj
  , `Effect4.Supervision.ForkEvent.registered.injEq
  , `Effect4.Supervision.ForkEvent.registered.noConfusion
  , `Effect4.Supervision.ForkEvent.registered.sizeOf_spec
  , `Effect4.Supervision.ForkEvent.scheduled
  , `Effect4.Supervision.ForkEvent.scheduled.elim
  , `Effect4.Supervision.ForkEvent.scheduled.inj
  , `Effect4.Supervision.ForkEvent.scheduled.injEq
  , `Effect4.Supervision.ForkEvent.scheduled.noConfusion
  , `Effect4.Supervision.ForkEvent.scheduled.sizeOf_spec
  , `Effect4.Supervision.ForkOptions
  , `Effect4.Supervision.ForkOptions.casesOn
  , `Effect4.Supervision.ForkOptions.ctorIdx
  , `Effect4.Supervision.ForkOptions.daemon
  , `Effect4.Supervision.ForkOptions.maskMode
  , `Effect4.Supervision.ForkOptions.mk
  , `Effect4.Supervision.ForkOptions.mk.inj
  , `Effect4.Supervision.ForkOptions.mk.injEq
  , `Effect4.Supervision.ForkOptions.mk.noConfusion
  , `Effect4.Supervision.ForkOptions.mk.sizeOf_spec
  , `Effect4.Supervision.ForkOptions.noConfusion
  , `Effect4.Supervision.ForkOptions.noConfusionType
  , `Effect4.Supervision.ForkOptions.rec
  , `Effect4.Supervision.ForkOptions.recOn
  , `Effect4.Supervision.ForkOptions.startImmediately
  , `Effect4.Supervision.ForkResult
  , `Effect4.Supervision.ForkResult.casesOn
  , `Effect4.Supervision.ForkResult.child
  , `Effect4.Supervision.ForkResult.ctorIdx
  , `Effect4.Supervision.ForkResult.events
  , `Effect4.Supervision.ForkResult.globals
  , `Effect4.Supervision.ForkResult.initial
  , `Effect4.Supervision.ForkResult.mk
  , `Effect4.Supervision.ForkResult.mk.inj
  , `Effect4.Supervision.ForkResult.mk.injEq
  , `Effect4.Supervision.ForkResult.mk.noConfusion
  , `Effect4.Supervision.ForkResult.mk.sizeOf_spec
  , `Effect4.Supervision.ForkResult.noConfusion
  , `Effect4.Supervision.ForkResult.noConfusionType
  , `Effect4.Supervision.ForkResult.parent
  , `Effect4.Supervision.ForkResult.rec
  , `Effect4.Supervision.ForkResult.recOn
  , `Effect4.Supervision.ForkResult.removeFromParent
  , `Effect4.Supervision.Globals
  , `Effect4.Supervision.Globals.Extends
  , `Effect4.Supervision.Globals.OwnsChildren
  , `Effect4.Supervision.Globals.OwnsChildren.eq_1
  , `Effect4.Supervision.Globals.Valid
  , `Effect4.Supervision.Globals.allocate
  , `Effect4.Supervision.Globals.allocate_eq
  , `Effect4.Supervision.Globals.allocated
  , `Effect4.Supervision.Globals.casesOn
  , `Effect4.Supervision.Globals.ctorIdx
  , `Effect4.Supervision.Globals.extends?
  , `Effect4.Supervision.Globals.extends?.eq_1
  , `Effect4.Supervision.Globals.extends?_iff
  , `Effect4.Supervision.Globals.extends_iff
  , `Effect4.Supervision.Globals.install
  , `Effect4.Supervision.Globals.install_eq
  , `Effect4.Supervision.Globals.middlewareInstalled
  , `Effect4.Supervision.Globals.mk
  , `Effect4.Supervision.Globals.mk.inj
  , `Effect4.Supervision.Globals.mk.injEq
  , `Effect4.Supervision.Globals.mk.noConfusion
  , `Effect4.Supervision.Globals.mk.sizeOf_spec
  , `Effect4.Supervision.Globals.noConfusion
  , `Effect4.Supervision.Globals.noConfusionType
  , `Effect4.Supervision.Globals.ownsChildren?
  , `Effect4.Supervision.Globals.ownsChildren?.eq_1
  , `Effect4.Supervision.Globals.ownsChildren?_iff
  , `Effect4.Supervision.Globals.ownsChildren_iff
  , `Effect4.Supervision.Globals.rec
  , `Effect4.Supervision.Globals.recOn
  , `Effect4.Supervision.Globals.valid_iff
  , `Effect4.Supervision.InterruptAction
  , `Effect4.Supervision.InterruptAction.awaitAll
  , `Effect4.Supervision.InterruptAction.awaitAll.elim
  , `Effect4.Supervision.InterruptAction.awaitAll.inj
  , `Effect4.Supervision.InterruptAction.awaitAll.injEq
  , `Effect4.Supervision.InterruptAction.awaitAll.noConfusion
  , `Effect4.Supervision.InterruptAction.awaitAll.sizeOf_spec
  , `Effect4.Supervision.InterruptAction.casesOn
  , `Effect4.Supervision.InterruptAction.ctorElim
  , `Effect4.Supervision.InterruptAction.ctorElimType
  , `Effect4.Supervision.InterruptAction.ctorIdx
  , `Effect4.Supervision.InterruptAction.noConfusion
  , `Effect4.Supervision.InterruptAction.noConfusionType
  , `Effect4.Supervision.InterruptAction.rec
  , `Effect4.Supervision.InterruptAction.recOn
  , `Effect4.Supervision.InterruptAction.request
  , `Effect4.Supervision.InterruptAction.request.elim
  , `Effect4.Supervision.InterruptAction.request.inj
  , `Effect4.Supervision.InterruptAction.request.injEq
  , `Effect4.Supervision.InterruptAction.request.noConfusion
  , `Effect4.Supervision.InterruptAction.request.sizeOf_spec
  , `Effect4.Supervision.MaskMode
  , `Effect4.Supervision.MaskMode.casesOn
  , `Effect4.Supervision.MaskMode.cases_receipt
  , `Effect4.Supervision.MaskMode.ctorElim
  , `Effect4.Supervision.MaskMode.ctorElimType
  , `Effect4.Supervision.MaskMode.ctorIdx
  , `Effect4.Supervision.MaskMode.inherit
  , `Effect4.Supervision.MaskMode.inherit.elim
  , `Effect4.Supervision.MaskMode.inherit.sizeOf_spec
  , `Effect4.Supervision.MaskMode.interruptible
  , `Effect4.Supervision.MaskMode.interruptible.elim
  , `Effect4.Supervision.MaskMode.interruptible.sizeOf_spec
  , `Effect4.Supervision.MaskMode.noConfusion
  , `Effect4.Supervision.MaskMode.noConfusionType
  , `Effect4.Supervision.MaskMode.ofNat
  , `Effect4.Supervision.MaskMode.ofNat_ctorIdx
  , `Effect4.Supervision.MaskMode.rec
  , `Effect4.Supervision.MaskMode.recOn
  , `Effect4.Supervision.MaskMode.select
  , `Effect4.Supervision.MaskMode.select.match_1
  , `Effect4.Supervision.MaskMode.select_inherit
  , `Effect4.Supervision.MaskMode.select_interruptible
  , `Effect4.Supervision.MaskMode.select_uninterruptible
  , `Effect4.Supervision.MaskMode.toCtorIdx
  , `Effect4.Supervision.MaskMode.uninterruptible
  , `Effect4.Supervision.MaskMode.uninterruptible.elim
  , `Effect4.Supervision.MaskMode.uninterruptible.sizeOf_spec
  , `Effect4.Supervision.Observation
  , `Effect4.Supervision.Observation.casesOn
  , `Effect4.Supervision.Observation.ctorElim
  , `Effect4.Supervision.Observation.ctorElimType
  , `Effect4.Supervision.Observation.ctorIdx
  , `Effect4.Supervision.Observation.effect
  , `Effect4.Supervision.Observation.effect.elim
  , `Effect4.Supervision.Observation.effect.inj
  , `Effect4.Supervision.Observation.effect.injEq
  , `Effect4.Supervision.Observation.effect.noConfusion
  , `Effect4.Supervision.Observation.effect.sizeOf_spec
  , `Effect4.Supervision.Observation.noConfusion
  , `Effect4.Supervision.Observation.noConfusionType
  , `Effect4.Supervision.Observation.rec
  , `Effect4.Supervision.Observation.recOn
  , `Effect4.Supervision.Observation.value
  , `Effect4.Supervision.Observation.value.elim
  , `Effect4.Supervision.Observation.value.inj
  , `Effect4.Supervision.Observation.value.injEq
  , `Effect4.Supervision.Observation.value.noConfusion
  , `Effect4.Supervision.Observation.value.sizeOf_spec
  , `Effect4.Supervision.Observation.waiting
  , `Effect4.Supervision.Observation.waiting.elim
  , `Effect4.Supervision.Observation.waiting.inj
  , `Effect4.Supervision.Observation.waiting.injEq
  , `Effect4.Supervision.Observation.waiting.noConfusion
  , `Effect4.Supervision.Observation.waiting.sizeOf_spec
  , `Effect4.Supervision.ObserverMode
  , `Effect4.Supervision.ObserverMode.awaitValue
  , `Effect4.Supervision.ObserverMode.awaitValue.elim
  , `Effect4.Supervision.ObserverMode.awaitValue.sizeOf_spec
  , `Effect4.Supervision.ObserverMode.casesOn
  , `Effect4.Supervision.ObserverMode.cases_receipt
  , `Effect4.Supervision.ObserverMode.ctorElim
  , `Effect4.Supervision.ObserverMode.ctorElimType
  , `Effect4.Supervision.ObserverMode.ctorIdx
  , `Effect4.Supervision.ObserverMode.joinEffect
  , `Effect4.Supervision.ObserverMode.joinEffect.elim
  , `Effect4.Supervision.ObserverMode.joinEffect.sizeOf_spec
  , `Effect4.Supervision.ObserverMode.noConfusion
  , `Effect4.Supervision.ObserverMode.noConfusionType
  , `Effect4.Supervision.ObserverMode.ofNat
  , `Effect4.Supervision.ObserverMode.ofNat_ctorIdx
  , `Effect4.Supervision.ObserverMode.rec
  , `Effect4.Supervision.ObserverMode.recOn
  , `Effect4.Supervision.ObserverMode.toCtorIdx
  , `Effect4.Supervision.RaceAllDecision
  , `Effect4.Supervision.RaceAllDecision.beginCleanup
  , `Effect4.Supervision.RaceAllDecision.beginCleanup.elim
  , `Effect4.Supervision.RaceAllDecision.beginCleanup.sizeOf_spec
  , `Effect4.Supervision.RaceAllDecision.beginLaunch
  , `Effect4.Supervision.RaceAllDecision.beginLaunch.elim
  , `Effect4.Supervision.RaceAllDecision.beginLaunch.sizeOf_spec
  , `Effect4.Supervision.RaceAllDecision.casesOn
  , `Effect4.Supervision.RaceAllDecision.complete
  , `Effect4.Supervision.RaceAllDecision.complete.elim
  , `Effect4.Supervision.RaceAllDecision.complete.inj
  , `Effect4.Supervision.RaceAllDecision.complete.injEq
  , `Effect4.Supervision.RaceAllDecision.complete.noConfusion
  , `Effect4.Supervision.RaceAllDecision.complete.sizeOf_spec
  , `Effect4.Supervision.RaceAllDecision.ctorElim
  , `Effect4.Supervision.RaceAllDecision.ctorElimType
  , `Effect4.Supervision.RaceAllDecision.ctorIdx
  , `Effect4.Supervision.RaceAllDecision.finishLaunch
  , `Effect4.Supervision.RaceAllDecision.finishLaunch.elim
  , `Effect4.Supervision.RaceAllDecision.finishLaunch.inj
  , `Effect4.Supervision.RaceAllDecision.finishLaunch.injEq
  , `Effect4.Supervision.RaceAllDecision.finishLaunch.noConfusion
  , `Effect4.Supervision.RaceAllDecision.finishLaunch.sizeOf_spec
  , `Effect4.Supervision.RaceAllDecision.noConfusion
  , `Effect4.Supervision.RaceAllDecision.noConfusionType
  , `Effect4.Supervision.RaceAllDecision.rec
  , `Effect4.Supervision.RaceAllDecision.recOn
  , `Effect4.Supervision.RaceAllDecision.requestNext
  , `Effect4.Supervision.RaceAllDecision.requestNext.elim
  , `Effect4.Supervision.RaceAllDecision.requestNext.sizeOf_spec
  , `Effect4.Supervision.RaceAllState
  , `Effect4.Supervision.RaceAllState.accepted
  , `Effect4.Supervision.RaceAllState.casesOn
  , `Effect4.Supervision.RaceAllState.cleanup
  , `Effect4.Supervision.RaceAllState.cleanupNeeded
  , `Effect4.Supervision.RaceAllState.cleanupRequested
  , `Effect4.Supervision.RaceAllState.ctorIdx
  , `Effect4.Supervision.RaceAllState.failures
  , `Effect4.Supervision.RaceAllState.initial
  , `Effect4.Supervision.RaceAllState.initial.eq_1
  , `Effect4.Supervision.RaceAllState.initial_eq
  , `Effect4.Supervision.RaceAllState.live
  , `Effect4.Supervision.RaceAllState.mk
  , `Effect4.Supervision.RaceAllState.mk.inj
  , `Effect4.Supervision.RaceAllState.mk.injEq
  , `Effect4.Supervision.RaceAllState.mk.noConfusion
  , `Effect4.Supervision.RaceAllState.mk.sizeOf_spec
  , `Effect4.Supervision.RaceAllState.noConfusion
  , `Effect4.Supervision.RaceAllState.noConfusionType
  , `Effect4.Supervision.RaceAllState.rec
  , `Effect4.Supervision.RaceAllState.recOn
  , `Effect4.Supervision.RaceAllState.remaining
  , `Effect4.Supervision.RaceAllState.requests
  , `Effect4.Supervision.RaceAllState.result?
  , `Effect4.Supervision.RaceAllState.result?.eq_1
  , `Effect4.Supervision.RaceAllState.result_eq
  , `Effect4.Supervision.RaceAllState.starting
  , `Effect4.Supervision.RaceAllState.unstarted
  , `Effect4.Supervision.RaceAllState.winner
  , `Effect4.Supervision.RaceRuns
  , `Effect4.Supervision.RaceRuns.eq_1
  , `Effect4.Supervision.RaceStep
  , `Effect4.Supervision.Refusal
  , `Effect4.Supervision.Refusal.casesOn
  , `Effect4.Supervision.Refusal.ctorElim
  , `Effect4.Supervision.Refusal.ctorElimType
  , `Effect4.Supervision.Refusal.ctorIdx
  , `Effect4.Supervision.Refusal.duplicateEntrant
  , `Effect4.Supervision.Refusal.duplicateEntrant.elim
  , `Effect4.Supervision.Refusal.duplicateEntrant.sizeOf_spec
  , `Effect4.Supervision.Refusal.duplicateFiber
  , `Effect4.Supervision.Refusal.duplicateFiber.elim
  , `Effect4.Supervision.Refusal.duplicateFiber.inj
  , `Effect4.Supervision.Refusal.duplicateFiber.injEq
  , `Effect4.Supervision.Refusal.duplicateFiber.noConfusion
  , `Effect4.Supervision.Refusal.duplicateFiber.sizeOf_spec
  , `Effect4.Supervision.Refusal.duplicateScopeKey
  , `Effect4.Supervision.Refusal.duplicateScopeKey.elim
  , `Effect4.Supervision.Refusal.duplicateScopeKey.inj
  , `Effect4.Supervision.Refusal.duplicateScopeKey.injEq
  , `Effect4.Supervision.Refusal.duplicateScopeKey.noConfusion
  , `Effect4.Supervision.Refusal.duplicateScopeKey.sizeOf_spec
  , `Effect4.Supervision.Refusal.duplicateSubscription
  , `Effect4.Supervision.Refusal.duplicateSubscription.elim
  , `Effect4.Supervision.Refusal.duplicateSubscription.inj
  , `Effect4.Supervision.Refusal.duplicateSubscription.injEq
  , `Effect4.Supervision.Refusal.duplicateSubscription.noConfusion
  , `Effect4.Supervision.Refusal.duplicateSubscription.sizeOf_spec
  , `Effect4.Supervision.Refusal.invalidChildOwnership
  , `Effect4.Supervision.Refusal.invalidChildOwnership.elim
  , `Effect4.Supervision.Refusal.invalidChildOwnership.sizeOf_spec
  , `Effect4.Supervision.Refusal.invalidFiber
  , `Effect4.Supervision.Refusal.invalidFiber.elim
  , `Effect4.Supervision.Refusal.invalidFiber.inj
  , `Effect4.Supervision.Refusal.invalidFiber.injEq
  , `Effect4.Supervision.Refusal.invalidFiber.noConfusion
  , `Effect4.Supervision.Refusal.invalidFiber.sizeOf_spec
  , `Effect4.Supervision.Refusal.invalidParentOwnership
  , `Effect4.Supervision.Refusal.invalidParentOwnership.elim
  , `Effect4.Supervision.Refusal.invalidParentOwnership.sizeOf_spec
  , `Effect4.Supervision.Refusal.invalidStartGlobals
  , `Effect4.Supervision.Refusal.invalidStartGlobals.elim
  , `Effect4.Supervision.Refusal.invalidStartGlobals.sizeOf_spec
  , `Effect4.Supervision.Refusal.noConfusion
  , `Effect4.Supervision.Refusal.noConfusionType
  , `Effect4.Supervision.Refusal.noEntrant
  , `Effect4.Supervision.Refusal.noEntrant.elim
  , `Effect4.Supervision.Refusal.noEntrant.sizeOf_spec
  , `Effect4.Supervision.Refusal.rec
  , `Effect4.Supervision.Refusal.recOn
  , `Effect4.Supervision.Refusal.unknownEntrant
  , `Effect4.Supervision.Refusal.unknownEntrant.elim
  , `Effect4.Supervision.Refusal.unknownEntrant.inj
  , `Effect4.Supervision.Refusal.unknownEntrant.injEq
  , `Effect4.Supervision.Refusal.unknownEntrant.noConfusion
  , `Effect4.Supervision.Refusal.unknownEntrant.sizeOf_spec
  , `Effect4.Supervision.Refusal.unknownPublication
  , `Effect4.Supervision.Refusal.unknownPublication.elim
  , `Effect4.Supervision.Refusal.unknownPublication.inj
  , `Effect4.Supervision.Refusal.unknownPublication.injEq
  , `Effect4.Supervision.Refusal.unknownPublication.noConfusion
  , `Effect4.Supervision.Refusal.unknownPublication.sizeOf_spec
  , `Effect4.Supervision.Refusal.wrongChildIdentity
  , `Effect4.Supervision.Refusal.wrongChildIdentity.elim
  , `Effect4.Supervision.Refusal.wrongChildIdentity.sizeOf_spec
  , `Effect4.Supervision.Refusal.wrongParentIdentity
  , `Effect4.Supervision.Refusal.wrongParentIdentity.elim
  , `Effect4.Supervision.Refusal.wrongParentIdentity.sizeOf_spec
  , `Effect4.Supervision.Refusal.wrongRacePhase
  , `Effect4.Supervision.Refusal.wrongRacePhase.elim
  , `Effect4.Supervision.Refusal.wrongRacePhase.sizeOf_spec
  , `Effect4.Supervision.Refusal.wrongStartMode
  , `Effect4.Supervision.Refusal.wrongStartMode.elim
  , `Effect4.Supervision.Refusal.wrongStartMode.sizeOf_spec
  , `Effect4.Supervision.ReplayResult
  , `Effect4.Supervision.ReplayResult.casesOn
  , `Effect4.Supervision.ReplayResult.ctorElim
  , `Effect4.Supervision.ReplayResult.ctorElimType
  , `Effect4.Supervision.ReplayResult.ctorIdx
  , `Effect4.Supervision.ReplayResult.done
  , `Effect4.Supervision.ReplayResult.done.elim
  , `Effect4.Supervision.ReplayResult.done.inj
  , `Effect4.Supervision.ReplayResult.done.injEq
  , `Effect4.Supervision.ReplayResult.done.noConfusion
  , `Effect4.Supervision.ReplayResult.done.sizeOf_spec
  , `Effect4.Supervision.ReplayResult.frontier
  , `Effect4.Supervision.ReplayResult.frontier.elim
  , `Effect4.Supervision.ReplayResult.frontier.inj
  , `Effect4.Supervision.ReplayResult.frontier.injEq
  , `Effect4.Supervision.ReplayResult.frontier.noConfusion
  , `Effect4.Supervision.ReplayResult.frontier.sizeOf_spec
  , `Effect4.Supervision.ReplayResult.noConfusion
  , `Effect4.Supervision.ReplayResult.noConfusionType
  , `Effect4.Supervision.ReplayResult.rec
  , `Effect4.Supervision.ReplayResult.recOn
  , `Effect4.Supervision.ReplayResult.refused
  , `Effect4.Supervision.ReplayResult.refused.elim
  , `Effect4.Supervision.ReplayResult.refused.inj
  , `Effect4.Supervision.ReplayResult.refused.injEq
  , `Effect4.Supervision.ReplayResult.refused.noConfusion
  , `Effect4.Supervision.ReplayResult.refused.sizeOf_spec
  , `Effect4.Supervision.ReplayResult.state
  , `Effect4.Supervision.ReplayResult.state.eq_1
  , `Effect4.Supervision.ReplayResult.state.eq_2
  , `Effect4.Supervision.ReplayResult.state.eq_3
  , `Effect4.Supervision.ReplayResult.state.match_1
  , `Effect4.Supervision.ReplayResult.state_done
  , `Effect4.Supervision.ReplayResult.state_frontier
  , `Effect4.Supervision.ReplayResult.state_refused
  , `Effect4.Supervision.ScopeBinding
  , `Effect4.Supervision.ScopeBinding.casesOn
  , `Effect4.Supervision.ScopeBinding.ctorIdx
  , `Effect4.Supervision.ScopeBinding.interruptor
  , `Effect4.Supervision.ScopeBinding.mk
  , `Effect4.Supervision.ScopeBinding.mk.inj
  , `Effect4.Supervision.ScopeBinding.mk.injEq
  , `Effect4.Supervision.ScopeBinding.mk.noConfusion
  , `Effect4.Supervision.ScopeBinding.mk.sizeOf_spec
  , `Effect4.Supervision.ScopeBinding.noConfusion
  , `Effect4.Supervision.ScopeBinding.noConfusionType
  , `Effect4.Supervision.ScopeBinding.observerKey
  , `Effect4.Supervision.ScopeBinding.rec
  , `Effect4.Supervision.ScopeBinding.recOn
  , `Effect4.Supervision.ScopeBinding.scope
  , `Effect4.Supervision.ScopeFinalizer
  , `Effect4.Supervision.ScopeFinalizer.casesOn
  , `Effect4.Supervision.ScopeFinalizer.child
  , `Effect4.Supervision.ScopeFinalizer.ctorIdx
  , `Effect4.Supervision.ScopeFinalizer.mk
  , `Effect4.Supervision.ScopeFinalizer.mk.inj
  , `Effect4.Supervision.ScopeFinalizer.mk.injEq
  , `Effect4.Supervision.ScopeFinalizer.mk.noConfusion
  , `Effect4.Supervision.ScopeFinalizer.mk.sizeOf_spec
  , `Effect4.Supervision.ScopeFinalizer.noConfusion
  , `Effect4.Supervision.ScopeFinalizer.noConfusionType
  , `Effect4.Supervision.ScopeFinalizer.rec
  , `Effect4.Supervision.ScopeFinalizer.recOn
  , `Effect4.Supervision.ScopeFinalizer.skipSelf
  , `Effect4.Supervision.ScopeMode
  , `Effect4.Supervision.ScopeMode.casesOn
  , `Effect4.Supervision.ScopeMode.cases_receipt
  , `Effect4.Supervision.ScopeMode.ctorElim
  , `Effect4.Supervision.ScopeMode.ctorElimType
  , `Effect4.Supervision.ScopeMode.ctorIdx
  , `Effect4.Supervision.ScopeMode.fiberRunIn
  , `Effect4.Supervision.ScopeMode.fiberRunIn.elim
  , `Effect4.Supervision.ScopeMode.fiberRunIn.sizeOf_spec
  , `Effect4.Supervision.ScopeMode.forkIn
  , `Effect4.Supervision.ScopeMode.forkIn.elim
  , `Effect4.Supervision.ScopeMode.forkIn.sizeOf_spec
  , `Effect4.Supervision.ScopeMode.noConfusion
  , `Effect4.Supervision.ScopeMode.noConfusionType
  , `Effect4.Supervision.ScopeMode.ofNat
  , `Effect4.Supervision.ScopeMode.ofNat_ctorIdx
  , `Effect4.Supervision.ScopeMode.rec
  , `Effect4.Supervision.ScopeMode.recOn
  , `Effect4.Supervision.ScopeMode.toCtorIdx
  , `Effect4.Supervision.StartObservation
  , `Effect4.Supervision.StartObservation.casesOn
  , `Effect4.Supervision.StartObservation.ctorElim
  , `Effect4.Supervision.StartObservation.ctorElimType
  , `Effect4.Supervision.StartObservation.ctorIdx
  , `Effect4.Supervision.StartObservation.deferred
  , `Effect4.Supervision.StartObservation.deferred.elim
  , `Effect4.Supervision.StartObservation.deferred.sizeOf_spec
  , `Effect4.Supervision.StartObservation.immediate
  , `Effect4.Supervision.StartObservation.immediate.elim
  , `Effect4.Supervision.StartObservation.immediate.inj
  , `Effect4.Supervision.StartObservation.immediate.injEq
  , `Effect4.Supervision.StartObservation.immediate.noConfusion
  , `Effect4.Supervision.StartObservation.immediate.sizeOf_spec
  , `Effect4.Supervision.StartObservation.noConfusion
  , `Effect4.Supervision.StartObservation.noConfusionType
  , `Effect4.Supervision.StartObservation.rec
  , `Effect4.Supervision.StartObservation.recOn
  , `Effect4.Supervision.Subscription
  , `Effect4.Supervision.Subscription.casesOn
  , `Effect4.Supervision.Subscription.ctorIdx
  , `Effect4.Supervision.Subscription.key
  , `Effect4.Supervision.Subscription.mk
  , `Effect4.Supervision.Subscription.mk.inj
  , `Effect4.Supervision.Subscription.mk.injEq
  , `Effect4.Supervision.Subscription.mk.noConfusion
  , `Effect4.Supervision.Subscription.mk.sizeOf_spec
  , `Effect4.Supervision.Subscription.mode
  , `Effect4.Supervision.Subscription.noConfusion
  , `Effect4.Supervision.Subscription.noConfusionType
  , `Effect4.Supervision.Subscription.rec
  , `Effect4.Supervision.Subscription.recOn
  , `Effect4.Supervision.WaitRuns
  , `Effect4.Supervision.WaitRuns.eq_1
  , `Effect4.Supervision.WaitState
  , `Effect4.Supervision.WaitState.begin
  , `Effect4.Supervision.WaitState.begin.eq_1
  , `Effect4.Supervision.WaitState.begin_eq
  , `Effect4.Supervision.WaitState.casesOn
  , `Effect4.Supervision.WaitState.ctorIdx
  , `Effect4.Supervision.WaitState.mk
  , `Effect4.Supervision.WaitState.mk.inj
  , `Effect4.Supervision.WaitState.mk.injEq
  , `Effect4.Supervision.WaitState.mk.noConfusion
  , `Effect4.Supervision.WaitState.mk.sizeOf_spec
  , `Effect4.Supervision.WaitState.noConfusion
  , `Effect4.Supervision.WaitState.noConfusionType
  , `Effect4.Supervision.WaitState.observe
  , `Effect4.Supervision.WaitState.observe.eq_1
  , `Effect4.Supervision.WaitState.observe_pending
  , `Effect4.Supervision.WaitState.observe_pending_membership
  , `Effect4.Supervision.WaitState.observe_unknown
  , `Effect4.Supervision.WaitState.pending
  , `Effect4.Supervision.WaitState.pending.eq_1
  , `Effect4.Supervision.WaitState.pending_eq
  , `Effect4.Supervision.WaitState.published
  , `Effect4.Supervision.WaitState.ready?
  , `Effect4.Supervision.WaitState.ready?.eq_1
  , `Effect4.Supervision.WaitState.ready_iff
  , `Effect4.Supervision.WaitState.ready_publications
  , `Effect4.Supervision.WaitState.rec
  , `Effect4.Supervision.WaitState.recOn
  , `Effect4.Supervision.WaitState.result
  , `Effect4.Supervision.WaitState.targets
  , `Effect4.Supervision.WaitStep
  , `Effect4.Supervision.awaitAllChildren
  , `Effect4.Supervision.awaitAllChildren_eq
  , `Effect4.Supervision.beginParentExit
  , `Effect4.Supervision.beginParentExit_eq
  , `Effect4.Supervision.bindScope
  , `Effect4.Supervision.bindScope.eq_1
  , `Effect4.Supervision.bindScope_closed
  , `Effect4.Supervision.bindScope_done
  , `Effect4.Supervision.bindScope_duplicate_key
  , `Effect4.Supervision.bindScope_invalid
  , `Effect4.Supervision.bindScope_open
  , `Effect4.Supervision.commitFork
  , `Effect4.Supervision.commitFork.eq_1
  , `Effect4.Supervision.commitFork_daemon_untracked
  , `Effect4.Supervision.commitFork_done_untracked
  , `Effect4.Supervision.commitFork_eq
  , `Effect4.Supervision.forkChild
  , `Effect4.Supervision.forkChild_eq
  , `Effect4.Supervision.forkDetach
  , `Effect4.Supervision.forkDetach_eq
  , `Effect4.Supervision.forkScopedBinding
  , `Effect4.Supervision.forkScopedBinding_eq
  , `Effect4.Supervision.forkUnsafe
  , `Effect4.Supervision.forkUnsafe.eq_1
  , `Effect4.Supervision.forkUnsafe.eq_2
  , `Effect4.Supervision.forkUnsafe.match_1
  , `Effect4.Supervision.forkUnsafe_allocated_nodup
  , `Effect4.Supervision.forkUnsafe_child_valid
  , `Effect4.Supervision.forkUnsafe_deferred
  , `Effect4.Supervision.forkUnsafe_duplicate
  , `Effect4.Supervision.forkUnsafe_fresh
  , `Effect4.Supervision.forkUnsafe_immediate
  , `Effect4.Supervision.forkUnsafe_invalid_child
  , `Effect4.Supervision.forkUnsafe_invalid_child_ownership
  , `Effect4.Supervision.forkUnsafe_invalid_globals
  , `Effect4.Supervision.forkUnsafe_invalid_ownership
  , `Effect4.Supervision.forkUnsafe_invalid_parent
  , `Effect4.Supervision.forkUnsafe_parent_children_nodup
  , `Effect4.Supervision.forkUnsafe_wrong_deferred
  , `Effect4.Supervision.forkUnsafe_wrong_identity
  , `Effect4.Supervision.forkUnsafe_wrong_immediate
  , `Effect4.Supervision.forkUnsafe_wrong_parent
  , `Effect4.Supervision.initialFiber
  , `Effect4.Supervision.initialFiber.eq_1
  , `Effect4.Supervision.initialFiber_eq
  , `Effect4.Supervision.initialFiber_valid
  , `Effect4.Supervision.instDecidableEqForkEvent
  , `Effect4.Supervision.instDecidableEqForkEvent.decEq
  , `Effect4.Supervision.instDecidableEqForkEvent.decEq.match_1
  , `Effect4.Supervision.instDecidableEqForkOptions
  , `Effect4.Supervision.instDecidableEqForkOptions.decEq
  , `Effect4.Supervision.instDecidableEqForkOptions.decEq.match_1
  , `Effect4.Supervision.instDecidableEqGlobals
  , `Effect4.Supervision.instDecidableEqGlobals.decEq
  , `Effect4.Supervision.instDecidableEqGlobals.decEq.match_1
  , `Effect4.Supervision.instDecidableEqInterruptAction
  , `Effect4.Supervision.instDecidableEqInterruptAction.decEq
  , `Effect4.Supervision.instDecidableEqInterruptAction.decEq.match_1
  , `Effect4.Supervision.instDecidableEqMaskMode
  , `Effect4.Supervision.instDecidableEqObserverMode
  , `Effect4.Supervision.instDecidableEqRefusal
  , `Effect4.Supervision.instDecidableEqRefusal.decEq
  , `Effect4.Supervision.instDecidableEqRefusal.decEq.match_1
  , `Effect4.Supervision.instDecidableEqScopeFinalizer
  , `Effect4.Supervision.instDecidableEqScopeFinalizer.decEq
  , `Effect4.Supervision.instDecidableEqScopeFinalizer.decEq.match_1
  , `Effect4.Supervision.instDecidableEqScopeMode
  , `Effect4.Supervision.instDecidableEqSubscription
  , `Effect4.Supervision.instDecidableEqSubscription.decEq
  , `Effect4.Supervision.instDecidableEqSubscription.decEq.match_1
  , `Effect4.Supervision.interruptAllRequests
  , `Effect4.Supervision.interruptAllRequests_eq
  , `Effect4.Supervision.interruptAllWait
  , `Effect4.Supervision.interruptAllWait_eq
  , `Effect4.Supervision.interruptCause
  , `Effect4.Supervision.interruptCause_eq
  , `Effect4.Supervision.newChildren
  , `Effect4.Supervision.newChildren.eq_1
  , `Effect4.Supervision.newChildren_eq
  , `Effect4.Supervision.newChildren_membership
  , `Effect4.Supervision.observation
  , `Effect4.Supervision.observation.match_1
  , `Effect4.Supervision.observation_await
  , `Effect4.Supervision.observation_join
  , `Effect4.Supervision.observation_value_ne_effect
  , `Effect4.Supervision.parentExitView
  , `Effect4.Supervision.parentExitView.eq_1
  , `Effect4.Supervision.parentExitView.match_1
  , `Effect4.Supervision.parentExitView_not_published_while_waiting
  , `Effect4.Supervision.parentExitView_publication_requires_children
  , `Effect4.Supervision.parentExitView_ready
  , `Effect4.Supervision.parentExitView_waiting
  , `Effect4.Supervision.raceAllAdmit
  , `Effect4.Supervision.raceAllAdmit_eq
  , `Effect4.Supervision.raceCleanupMask
  , `Effect4.Supervision.raceCleanupMask_eq
  , `Effect4.Supervision.raceComplete
  , `Effect4.Supervision.raceComplete.eq_1
  , `Effect4.Supervision.raceComplete.match_1
  , `Effect4.Supervision.raceComplete_after_accepted
  , `Effect4.Supervision.raceComplete_failure_last
  , `Effect4.Supervision.raceComplete_failure_pending
  , `Effect4.Supervision.raceComplete_success
  , `Effect4.Supervision.raceComplete_unknown
  , `Effect4.Supervision.raceForkOptions
  , `Effect4.Supervision.raceForkOptions_eq
  , `Effect4.Supervision.raceReplay
  , `Effect4.Supervision.raceReplay.eq_1
  , `Effect4.Supervision.raceReplay.eq_2
  , `Effect4.Supervision.raceReplay.eq_def
  , `Effect4.Supervision.raceReplay.match_1
  , `Effect4.Supervision.raceReplay.match_3
  , `Effect4.Supervision.raceReplay_cons_error
  , `Effect4.Supervision.raceReplay_cons_ok
  , `Effect4.Supervision.raceReplay_frontier
  , `Effect4.Supervision.raceReplay_ready
  , `Effect4.Supervision.raceRuns_iff
  , `Effect4.Supervision.raceStep
  , `Effect4.Supervision.raceStep.eq_1
  , `Effect4.Supervision.raceStep.eq_2
  , `Effect4.Supervision.raceStep.eq_3
  , `Effect4.Supervision.raceStep.eq_4
  , `Effect4.Supervision.raceStep.eq_5
  , `Effect4.Supervision.raceStep.match_1
  , `Effect4.Supervision.raceStep.match_3
  , `Effect4.Supervision.raceStep.match_5
  , `Effect4.Supervision.raceStep_begin
  , `Effect4.Supervision.raceStep_beginCleanup
  , `Effect4.Supervision.raceStep_beginCleanup_blocked
  , `Effect4.Supervision.raceStep_begin_blocked
  , `Effect4.Supervision.raceStep_begin_empty
  , `Effect4.Supervision.raceStep_complete
  , `Effect4.Supervision.raceStep_complete_unknown
  , `Effect4.Supervision.raceStep_finish_done
  , `Effect4.Supervision.raceStep_finish_duplicate
  , `Effect4.Supervision.raceStep_finish_live
  , `Effect4.Supervision.raceStep_finish_missing
  , `Effect4.Supervision.raceStep_iff
  , `Effect4.Supervision.raceStep_requestNext
  , `Effect4.Supervision.raceStep_requestNext_blocked
  , `Effect4.Supervision.race_cleanup_result_requires_publications
  , `Effect4.Supervision.race_empty_frontier
  , `Effect4.Supervision.race_first_accepted_stable
  , `Effect4.Supervision.race_fixedTape_deterministic
  , `Effect4.Supervision.race_result_requires_start_finished
  , `Effect4.Supervision.race_single_success
  , `Effect4.Supervision.race_two_failures
  , `Effect4.Supervision.scopeFinalizerInterruptor
  , `Effect4.Supervision.scopeFinalizerInterruptor.eq_1
  , `Effect4.Supervision.scopeFinalizerInterruptor_eq
  , `Effect4.Supervision.scopeFinalizer_self_guard
  , `Effect4.Supervision.scopeObserver
  , `Effect4.Supervision.scopeObserver.eq_1
  , `Effect4.Supervision.scopeObserver_eq
  , `Effect4.Supervision.scopeObserver_key_membership
  , `Effect4.Supervision.waitReplay
  , `Effect4.Supervision.waitReplay.eq_1
  , `Effect4.Supervision.waitReplay.eq_2
  , `Effect4.Supervision.waitReplay.eq_def
  , `Effect4.Supervision.waitReplay.match_1
  , `Effect4.Supervision.waitReplay.match_3
  , `Effect4.Supervision.waitReplay.match_5
  , `Effect4.Supervision.waitReplay_cons_error
  , `Effect4.Supervision.waitReplay_cons_ok
  , `Effect4.Supervision.waitReplay_done_ready
  , `Effect4.Supervision.waitReplay_frame
  , `Effect4.Supervision.waitReplay_frontier
  , `Effect4.Supervision.waitReplay_ready
  , `Effect4.Supervision.waitRuns_iff
  , `Effect4.Supervision.waitStep_iff
  , `Effect4.Supervision.wait_fixedTape_deterministic
  , `Effect4.Supervision.wait_two_publications
  ]

private def supervisionApi :=
  [ (`Effect4.Supervision.MaskMode, "SUP-L-MASK")
  , (`Effect4.Supervision.MaskMode.interruptible, "SUP-L-MASK")
  , (`Effect4.Supervision.MaskMode.uninterruptible, "SUP-L-MASK")
  , (`Effect4.Supervision.MaskMode.inherit, "SUP-L-MASK")
  , (`Effect4.Supervision.ForkOptions, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkOptions.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkOptions.startImmediately, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkOptions.daemon, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkOptions.maskMode, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.allocated, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.middlewareInstalled, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ObserverMode, "SUP-L-OBSERVER")
  , (`Effect4.Supervision.ObserverMode.awaitValue, "SUP-L-OBSERVER")
  , (`Effect4.Supervision.ObserverMode.joinEffect, "SUP-L-OBSERVER")
  , (`Effect4.Supervision.Subscription, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Subscription.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Subscription.key, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Subscription.mode, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.core, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.context, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.children, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.subscriptions, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.interrupted, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Observation, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Observation.waiting, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Observation.value, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Observation.effect, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.StartObservation, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.StartObservation.deferred, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.StartObservation.immediate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkEvent, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkEvent.scheduled, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkEvent.evaluated, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkEvent.registered, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.globals, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.parent, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.initial, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.child, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.events, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ForkResult.removeFromParent, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.InterruptAction, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.InterruptAction.request, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.InterruptAction.awaitAll, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.invalidFiber, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.duplicateFiber, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.wrongStartMode, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.wrongChildIdentity, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.wrongParentIdentity, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.invalidStartGlobals, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.invalidParentOwnership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.invalidChildOwnership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.duplicateSubscription, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.unknownPublication, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.duplicateScopeKey, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.duplicateEntrant, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.noEntrant, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.wrongRacePhase, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Refusal.unknownEntrant, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.targets, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.published, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.result, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.done, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.frontier, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.refused, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeMode, "SUP-L-SCOPE")
  , (`Effect4.Supervision.ScopeMode.forkIn, "SUP-L-SCOPE")
  , (`Effect4.Supervision.ScopeMode.fiberRunIn, "SUP-L-SCOPE")
  , (`Effect4.Supervision.ScopeFinalizer, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeFinalizer.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeFinalizer.child, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeFinalizer.skipSelf, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeBinding, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeBinding.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeBinding.scope, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeBinding.observerKey, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ScopeBinding.interruptor, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.mk, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.unstarted, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.starting, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.live, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.remaining, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.failures, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.winner, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.accepted, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.cleanupNeeded, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.requests, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.cleanup, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.cleanupRequested, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllDecision, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllDecision.beginLaunch, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllDecision.finishLaunch, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllDecision.complete, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllDecision.beginCleanup, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllDecision.requestNext, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.MaskMode.select, "SUP-L-MASK")
  , (`Effect4.Supervision.Globals.install, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.Valid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.allocate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.Extends, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.extends?, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.OwnsChildren, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.ownsChildren?, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.Valid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.valid?, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.toFiberState, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.published?, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.addChild, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.removeChild, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.observation, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.observe, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.cancel, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.publish, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.interruptCause, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.recordInterrupt, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.initialFiber, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.commitFork, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkChild, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkDetach, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.begin, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.pending, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.ready?, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.observe, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.state, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitStep, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitRuns, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.beginParentExit, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.parentExitView, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.newChildren, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.awaitAllChildren, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.interruptAllRequests, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.interruptAllWait, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.bindScope, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkScopedBinding, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.scopeFinalizerInterruptor, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.scopeObserver, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceForkOptions, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceCleanupMask, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.initial, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceAllAdmit, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.result?, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceComplete, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceStep, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceReplay, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceRuns, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.MaskMode.select_interruptible, "SUP-L-MASK")
  , (`Effect4.Supervision.MaskMode.select_uninterruptible, "SUP-L-MASK")
  , (`Effect4.Supervision.MaskMode.select_inherit, "SUP-L-MASK")
  , (`Effect4.Supervision.MaskMode.cases_receipt, "SUP-L-MASK")
  , (`Effect4.Supervision.ObserverMode.cases_receipt, "SUP-L-OBSERVER")
  , (`Effect4.Supervision.ScopeMode.cases_receipt, "SUP-L-SCOPE")
  , (`Effect4.Supervision.Globals.install_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.valid_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.ownsChildren_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.valid_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.valid?_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.toFiberState_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.published_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.published_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.addChild_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.removeChild_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.addChild_nodup, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.removeChild_membership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.observation_await, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.observation_join, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.observation_value_ne_effect, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.observe_invalid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.observe_done, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.observe_live, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.observe_duplicate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.cancel_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.cancel_membership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.publish_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.publish_valid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.interruptCause_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.recordInterrupt_done, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.recordInterrupt_live, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Fiber.recordInterrupt_core, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.initialFiber_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.initialFiber_valid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.commitFork_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_duplicate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_deferred, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_wrong_deferred, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_wrong_immediate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_wrong_identity, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_wrong_parent, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_invalid_child, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_invalid_parent, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_invalid_globals, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_invalid_ownership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_invalid_child_ownership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_immediate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_fresh, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_allocated_nodup, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_child_valid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkUnsafe_parent_children_nodup, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkChild_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkDetach_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.commitFork_done_untracked, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.commitFork_daemon_untracked, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.allocate_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.extends_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.extends?_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.Globals.ownsChildren?_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.begin_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.pending_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.ready_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.ready_publications, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.observe_pending, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.observe_unknown, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.WaitState.observe_pending_membership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitStep_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitRuns_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.state_done, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.state_frontier, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.ReplayResult.state_refused, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay_ready, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay_frontier, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay_cons_ok, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay_cons_error, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.wait_fixedTape_deterministic, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay_done_ready, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.waitReplay_frame, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.wait_two_publications, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.beginParentExit_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.parentExitView_waiting, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.parentExitView_ready, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.parentExitView_not_published_while_waiting, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.parentExitView_publication_requires_children, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.newChildren_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.newChildren_membership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.awaitAllChildren_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.interruptAllRequests_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.interruptAllWait_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.bindScope_invalid, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.bindScope_done, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.bindScope_closed, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.bindScope_duplicate_key, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.bindScope_open, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.forkScopedBinding_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.scopeFinalizerInterruptor_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.scopeFinalizer_self_guard, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.scopeObserver_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.scopeObserver_key_membership, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceForkOptions_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceCleanupMask_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.initial_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceAllAdmit_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.RaceAllState.result_eq, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceComplete_unknown, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceComplete_after_accepted, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceComplete_success, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceComplete_failure_last, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceComplete_failure_pending, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_begin_blocked, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_begin_empty, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_begin, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_finish_missing, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_finish_duplicate, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_finish_live, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_finish_done, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_complete, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_complete_unknown, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_beginCleanup, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_beginCleanup_blocked, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_requestNext, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_requestNext_blocked, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceStep_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceRuns_iff, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceReplay_ready, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceReplay_frontier, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceReplay_cons_ok, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.raceReplay_cons_error, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_fixedTape_deterministic, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_first_accepted_stable, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_result_requires_start_finished, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_cleanup_result_requires_publications, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_empty_frontier, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_single_success, "SUPERVISION-PG-RC112")
  , (`Effect4.Supervision.race_two_failures, "SUPERVISION-PG-RC112")
  ]

private def supervisionTheorems :=
  [ (`Effect4.Supervision.MaskMode.select_interruptible, "none", "fork.unsafe")
  , (`Effect4.Supervision.MaskMode.select_uninterruptible, "none", "fork.unsafe")
  , (`Effect4.Supervision.MaskMode.select_inherit, "none", "fork.unsafe")
  , (`Effect4.Supervision.MaskMode.cases_receipt, "propext", "fork.unsafe")
  , (`Effect4.Supervision.ObserverMode.cases_receipt, "propext", "fork.await fork.join")
  , (`Effect4.Supervision.ScopeMode.cases_receipt, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.Globals.install_eq, "none", "fork.child rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.Globals.valid_iff, "none", "fork.unsafe")
  , (`Effect4.Supervision.Globals.ownsChildren_iff, "none", "fork.unsafe rule.only-fork-child-tracks")
  , (`Effect4.Supervision.Fiber.valid_iff, "none", "fork.unsafe fork.join")
  , (`Effect4.Supervision.Fiber.valid?_iff, "propext", "fork.unsafe fork.join")
  , (`Effect4.Supervision.Fiber.toFiberState_eq, "none", "fork.unsafe fork.join")
  , (`Effect4.Supervision.Fiber.published_iff, "propext", "fork.join fork.await rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.Fiber.published_eq, "none", "fork.join fork.await")
  , (`Effect4.Supervision.Fiber.addChild_eq, "propext", "rule.only-fork-child-tracks")
  , (`Effect4.Supervision.Fiber.removeChild_eq, "none", "fork.child rule.only-fork-child-tracks")
  , (`Effect4.Supervision.Fiber.addChild_nodup, "propext,Quot.sound", "fork.child rule.only-fork-child-tracks")
  , (`Effect4.Supervision.Fiber.removeChild_membership, "propext,Quot.sound", "fork.child rule.only-fork-child-tracks")
  , (`Effect4.Supervision.observation_await, "none", "fork.await")
  , (`Effect4.Supervision.observation_join, "none", "fork.join")
  , (`Effect4.Supervision.observation_value_ne_effect, "none", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.observe_invalid, "propext,Quot.sound", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.observe_done, "propext,Quot.sound", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.observe_live, "propext,Quot.sound", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.observe_duplicate, "propext,Quot.sound", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.cancel_eq, "none", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.cancel_membership, "propext,Quot.sound", "fork.await fork.join")
  , (`Effect4.Supervision.Fiber.publish_eq, "none", "fork.await fork.join rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.Fiber.publish_valid, "propext", "fork.await fork.join")
  , (`Effect4.Supervision.interruptCause_eq, "propext,Quot.sound", "fork.interrupt interrupt.accumulate")
  , (`Effect4.Supervision.Fiber.recordInterrupt_done, "propext,Quot.sound", "fork.interrupt interrupt.accumulate")
  , (`Effect4.Supervision.Fiber.recordInterrupt_live, "propext,Quot.sound", "interrupt.accumulate fork.interrupt")
  , (`Effect4.Supervision.Fiber.recordInterrupt_core, "propext,Quot.sound", "fork.interrupt interrupt.accumulate")
  , (`Effect4.Supervision.initialFiber_eq, "none", "fork.unsafe")
  , (`Effect4.Supervision.initialFiber_valid, "propext", "fork.unsafe")
  , (`Effect4.Supervision.commitFork_eq, "propext", "fork.unsafe rule.only-fork-child-tracks")
  , (`Effect4.Supervision.forkUnsafe_duplicate, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_deferred, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_wrong_deferred, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_wrong_immediate, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_wrong_identity, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_wrong_parent, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_invalid_child, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_invalid_parent, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_invalid_globals, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_invalid_ownership, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_invalid_child_ownership, "propext,Quot.sound", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_immediate, "propext,Quot.sound", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_fresh, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_allocated_nodup, "propext,Quot.sound", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_child_valid, "propext", "fork.unsafe")
  , (`Effect4.Supervision.forkUnsafe_parent_children_nodup, "propext,Quot.sound", "fork.child rule.only-fork-child-tracks")
  , (`Effect4.Supervision.forkChild_eq, "propext", "fork.child rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.forkDetach_eq, "propext", "fork.detach rule.only-fork-child-tracks")
  , (`Effect4.Supervision.commitFork_done_untracked, "propext", "fork.unsafe fork.child")
  , (`Effect4.Supervision.commitFork_daemon_untracked, "propext", "fork.detach rule.only-fork-child-tracks")
  , (`Effect4.Supervision.Globals.allocate_eq, "none", "fork.unsafe")
  , (`Effect4.Supervision.Globals.extends_iff, "none", "fork.unsafe fork.child")
  , (`Effect4.Supervision.Globals.extends?_iff, "propext", "fork.unsafe fork.child")
  , (`Effect4.Supervision.Globals.ownsChildren?_iff, "propext,Quot.sound", "fork.unsafe fork.child")
  , (`Effect4.Supervision.WaitState.begin_eq, "none", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.WaitState.pending_eq, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.WaitState.ready_iff, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.WaitState.ready_publications, "propext,Quot.sound", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.WaitState.observe_pending, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.WaitState.observe_unknown, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.WaitState.observe_pending_membership, "propext,Quot.sound", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitStep_iff, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitRuns_iff, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.ReplayResult.state_done, "none", "rule.children-interrupted-after-exit fork.race-all")
  , (`Effect4.Supervision.ReplayResult.state_frontier, "none", "rule.children-interrupted-after-exit fork.race-all")
  , (`Effect4.Supervision.ReplayResult.state_refused, "none", "rule.children-interrupted-after-exit fork.race-all")
  , (`Effect4.Supervision.waitReplay_ready, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitReplay_frontier, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitReplay_cons_ok, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitReplay_cons_error, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.wait_fixedTape_deterministic, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitReplay_done_ready, "propext", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.waitReplay_frame, "propext,Quot.sound", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.wait_two_publications, "propext,Quot.sound", "rule.children-interrupted-after-exit fork.interrupt-all fork.race-all")
  , (`Effect4.Supervision.beginParentExit_eq, "none", "fork.child rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.parentExitView_waiting, "propext", "rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.parentExitView_ready, "propext", "rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.parentExitView_not_published_while_waiting, "propext", "rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.parentExitView_publication_requires_children, "propext,Quot.sound", "rule.children-interrupted-after-exit")
  , (`Effect4.Supervision.newChildren_eq, "propext", "fork.await-all-children")
  , (`Effect4.Supervision.newChildren_membership, "propext,Quot.sound", "fork.await-all-children")
  , (`Effect4.Supervision.awaitAllChildren_eq, "propext", "fork.await-all-children")
  , (`Effect4.Supervision.interruptAllRequests_eq, "none", "fork.interrupt-all fork.interrupt")
  , (`Effect4.Supervision.interruptAllWait_eq, "none", "fork.interrupt-all fork.interrupt")
  , (`Effect4.Supervision.bindScope_invalid, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.bindScope_done, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.bindScope_closed, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.bindScope_duplicate_key, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.bindScope_open, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.forkScopedBinding_eq, "propext", "fork.scoped")
  , (`Effect4.Supervision.scopeFinalizerInterruptor_eq, "none", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.scopeFinalizer_self_guard, "propext", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.scopeObserver_eq, "none", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.scopeObserver_key_membership, "propext,Quot.sound", "fork.in fork.fiber-run-in")
  , (`Effect4.Supervision.raceForkOptions_eq, "none", "fork.race-all rule.only-fork-child-tracks")
  , (`Effect4.Supervision.raceCleanupMask_eq, "none", "fork.race-all")
  , (`Effect4.Supervision.RaceAllState.initial_eq, "none", "fork.race-all")
  , (`Effect4.Supervision.raceAllAdmit_eq, "none", "fork.race-all")
  , (`Effect4.Supervision.RaceAllState.result_eq, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceComplete_unknown, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceComplete_after_accepted, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.raceComplete_success, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.raceComplete_failure_last, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.raceComplete_failure_pending, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.raceStep_begin_blocked, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_begin_empty, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_begin, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_finish_missing, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_finish_duplicate, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_finish_live, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_finish_done, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_complete, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_complete_unknown, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_beginCleanup, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_beginCleanup_blocked, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_requestNext, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_requestNext_blocked, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceStep_iff, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceRuns_iff, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceReplay_ready, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceReplay_frontier, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceReplay_cons_ok, "propext", "fork.race-all")
  , (`Effect4.Supervision.raceReplay_cons_error, "propext", "fork.race-all")
  , (`Effect4.Supervision.race_fixedTape_deterministic, "propext", "fork.race-all")
  , (`Effect4.Supervision.race_first_accepted_stable, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.race_result_requires_start_finished, "propext", "fork.race-all")
  , (`Effect4.Supervision.race_cleanup_result_requires_publications, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.race_empty_frontier, "propext", "fork.race-all")
  , (`Effect4.Supervision.race_single_success, "propext,Quot.sound", "fork.race-all")
  , (`Effect4.Supervision.race_two_failures, "propext,Quot.sound", "fork.race-all")
  ]

private def supervisionShapes : List (Name × List Name × Option (List Name)) :=
  [ (`Effect4.Supervision.MaskMode, [ `Effect4.Supervision.MaskMode.interruptible, `Effect4.Supervision.MaskMode.uninterruptible, `Effect4.Supervision.MaskMode.inherit ], none)
  , (`Effect4.Supervision.ForkOptions, [ `Effect4.Supervision.ForkOptions.mk ], some [ `startImmediately, `daemon, `maskMode ])
  , (`Effect4.Supervision.Globals, [ `Effect4.Supervision.Globals.mk ], some [ `allocated, `middlewareInstalled ])
  , (`Effect4.Supervision.ObserverMode, [ `Effect4.Supervision.ObserverMode.awaitValue, `Effect4.Supervision.ObserverMode.joinEffect ], none)
  , (`Effect4.Supervision.Subscription, [ `Effect4.Supervision.Subscription.mk ], some [ `key, `mode ])
  , (`Effect4.Supervision.Fiber, [ `Effect4.Supervision.Fiber.mk ], some [ `core, `context, `children, `subscriptions, `interrupted ])
  , (`Effect4.Supervision.Observation, [ `Effect4.Supervision.Observation.waiting, `Effect4.Supervision.Observation.value, `Effect4.Supervision.Observation.effect ], none)
  , (`Effect4.Supervision.StartObservation, [ `Effect4.Supervision.StartObservation.deferred, `Effect4.Supervision.StartObservation.immediate ], none)
  , (`Effect4.Supervision.ForkEvent, [ `Effect4.Supervision.ForkEvent.scheduled, `Effect4.Supervision.ForkEvent.evaluated, `Effect4.Supervision.ForkEvent.registered ], none)
  , (`Effect4.Supervision.ForkResult, [ `Effect4.Supervision.ForkResult.mk ], some [ `globals, `parent, `initial, `child, `events, `removeFromParent ])
  , (`Effect4.Supervision.InterruptAction, [ `Effect4.Supervision.InterruptAction.request, `Effect4.Supervision.InterruptAction.awaitAll ], none)
  , (`Effect4.Supervision.Refusal, [ `Effect4.Supervision.Refusal.invalidFiber, `Effect4.Supervision.Refusal.duplicateFiber, `Effect4.Supervision.Refusal.wrongStartMode, `Effect4.Supervision.Refusal.wrongChildIdentity, `Effect4.Supervision.Refusal.wrongParentIdentity, `Effect4.Supervision.Refusal.invalidStartGlobals, `Effect4.Supervision.Refusal.invalidParentOwnership, `Effect4.Supervision.Refusal.invalidChildOwnership, `Effect4.Supervision.Refusal.duplicateSubscription, `Effect4.Supervision.Refusal.unknownPublication, `Effect4.Supervision.Refusal.duplicateScopeKey, `Effect4.Supervision.Refusal.duplicateEntrant, `Effect4.Supervision.Refusal.noEntrant, `Effect4.Supervision.Refusal.wrongRacePhase, `Effect4.Supervision.Refusal.unknownEntrant ], none)
  , (`Effect4.Supervision.WaitState, [ `Effect4.Supervision.WaitState.mk ], some [ `targets, `published, `result ])
  , (`Effect4.Supervision.ReplayResult, [ `Effect4.Supervision.ReplayResult.done, `Effect4.Supervision.ReplayResult.frontier, `Effect4.Supervision.ReplayResult.refused ], none)
  , (`Effect4.Supervision.ScopeMode, [ `Effect4.Supervision.ScopeMode.forkIn, `Effect4.Supervision.ScopeMode.fiberRunIn ], none)
  , (`Effect4.Supervision.ScopeFinalizer, [ `Effect4.Supervision.ScopeFinalizer.mk ], some [ `child, `skipSelf ])
  , (`Effect4.Supervision.ScopeBinding, [ `Effect4.Supervision.ScopeBinding.mk ], some [ `scope, `observerKey, `interruptor ])
  , (`Effect4.Supervision.RaceAllState, [ `Effect4.Supervision.RaceAllState.mk ], some [ `unstarted, `starting, `live, `remaining, `failures, `winner, `accepted, `cleanupNeeded, `requests, `cleanup, `cleanupRequested ])
  , (`Effect4.Supervision.RaceAllDecision, [ `Effect4.Supervision.RaceAllDecision.beginLaunch, `Effect4.Supervision.RaceAllDecision.finishLaunch, `Effect4.Supervision.RaceAllDecision.complete, `Effect4.Supervision.RaceAllDecision.beginCleanup, `Effect4.Supervision.RaceAllDecision.requestNext ], none)
  ]

private def supervisionTypes :=
  [ ("SUP-TYPE-MaskMode", `Effect4.Supervision.MaskMode, "native finite leaf", "SUP-L-MASK")
  , ("SUP-TYPE-ForkOptions", `Effect4.Supervision.ForkOptions, "native options data", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Globals", `Effect4.Supervision.Globals, "native global view", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-ObserverMode", `Effect4.Supervision.ObserverMode, "native finite leaf", "SUP-L-OBSERVER")
  , ("SUP-TYPE-Subscription", `Effect4.Supervision.Subscription, "native observer handle", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Fiber", `Effect4.Supervision.Fiber, "native related view", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Observation", `Effect4.Supervision.Observation, "native result observation", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-StartObservation", `Effect4.Supervision.StartObservation, "native external decision data", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-ForkEvent", `Effect4.Supervision.ForkEvent, "native boundary trace", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-ForkResult", `Effect4.Supervision.ForkResult, "native result data", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-InterruptAction", `Effect4.Supervision.InterruptAction, "native call-plan alphabet", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Refusal", `Effect4.Supervision.Refusal, "native controller refusal", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-WaitState", `Effect4.Supervision.WaitState, "native shared controller", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-ReplayResult", `Effect4.Supervision.ReplayResult, "native controller outcome", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-ScopeMode", `Effect4.Supervision.ScopeMode, "native finite leaf", "SUP-L-SCOPE")
  , ("SUP-TYPE-ScopeFinalizer", `Effect4.Supervision.ScopeFinalizer, "native first-order instruction", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-ScopeBinding", `Effect4.Supervision.ScopeBinding, "native related result", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-RaceAllState", `Effect4.Supervision.RaceAllState, "native controller state", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-RaceAllDecision", `Effect4.Supervision.RaceAllDecision, "native decision alphabet", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Globals.Valid", `Effect4.Supervision.Globals.Valid, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Globals.Extends", `Effect4.Supervision.Globals.Extends, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Globals.OwnsChildren", `Effect4.Supervision.Globals.OwnsChildren, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-Fiber.Valid", `Effect4.Supervision.Fiber.Valid, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-WaitStep", `Effect4.Supervision.WaitStep, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-WaitRuns", `Effect4.Supervision.WaitRuns, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-RaceStep", `Effect4.Supervision.RaceStep, "native Prop judgment", "SUPERVISION-PG-RC112")
  , ("SUP-TYPE-RaceRuns", `Effect4.Supervision.RaceRuns, "native Prop judgment", "SUPERVISION-PG-RC112")
  ]

private def supervisionLeaves :=
  [ ("SUP-L-MASK", `Effect4.Supervision.MaskMode, `Effect4.Supervision.MaskMode.cases_receipt)
  , ("SUP-L-OBSERVER", `Effect4.Supervision.ObserverMode, `Effect4.Supervision.ObserverMode.cases_receipt)
  , ("SUP-L-SCOPE", `Effect4.Supervision.ScopeMode, `Effect4.Supervision.ScopeMode.cases_receipt)
  ]

private def supervisionEdges :=
  [ ("IDENTITY", "census+dispositions+shapes", "required-local")
  , ("CONSTRUCTION", "initialization+admission+refusal+finite-leaves", "required-local")
  , ("SEMANTICS", "WaitStep+WaitRuns+RaceStep+RaceRuns+inhabited-runs", "required-local")
  , ("LAWS", "publication+identity+fixed-tape+accepted-result", "required-local")
  , ("REPRESENTATION", "no-codec-or-generated-program-claim", "not-applicable")
  , ("COUNTEREXAMPLES", "E4-CONC-CE-012..026", "required-local")
  , ("BRIDGES", "source-body+context+continuation+scope+shared-set", "required-open")
  , ("TARGETS", "finite-host-cases-do-not-close-interpretation", "required-open")
  , ("TRUST", "136-local-axiom-receipts+bound-repository-trust-receipt-pending", "required-open")
  , ("COVERAGE", "exact-public-ownership-and-assurance-routes", "required-local")
  ]

private def checkSupervisionShape (typeName : Name) (constructors : List Name)
    (fields : Option (List Name)) : CommandElabM Unit := do
  let environment ← getEnv
  let information ← match environment.find? typeName with
    | some (.inductInfo info) => pure info
    | some _ => failJoin m!"supervision shape: {typeName} is not an inductive declaration"
    | none => failJoin m!"supervision shape: missing {typeName}"
  unless information.all == [typeName] && information.ctors == constructors do
    failJoin m!"supervision constructor shape for {typeName}: {information.ctors}"
  match fields with
  | none =>
    if (getStructureInfo? environment typeName).isSome then
      failJoin m!"supervision shape: unexpected structure {typeName}"
  | some expected =>
    let some structureInfo := getStructureInfo? environment typeName
      | failJoin m!"supervision shape: missing structure metadata for {typeName}"
    unless structureInfo.fieldNames.toList == expected do
      failJoin m!"supervision structure field shape for {typeName}: expected {expected}, found {structureInfo.fieldNames}"

private def supervisionRoute (name : Name) : String :=
  if `Effect4.Supervision.MaskMode |>.isPrefixOf name then "SUP-L-MASK"
  else if `Effect4.Supervision.ObserverMode |>.isPrefixOf name then "SUP-L-OBSERVER"
  else if `Effect4.Supervision.ScopeMode |>.isPrefixOf name then "SUP-L-SCOPE"
  else if `Effect4.Supervision.instDecidableEqMaskMode |>.isPrefixOf name then "SUP-L-MASK"
  else if `Effect4.Supervision.instDecidableEqObserverMode |>.isPrefixOf name then "SUP-L-OBSERVER"
  else if `Effect4.Supervision.instDecidableEqScopeMode |>.isPrefixOf name then "SUP-L-SCOPE"
  else "SUPERVISION-PG-RC112"

private def checkSupervisionAssurance : CommandElabM Unit := do
  let owner := `Effect4.Concurrency.Supervision
  checkExactModuleSurface owner supervisionOwned
  checkUniqueNames "supervision authored API" (supervisionApi.map Prod.fst)
  checkUniqueNames "supervision theorem receipt" (supervisionTheorems.map Prod.fst)
  checkUniqueNames "supervision type disposition" (supervisionTypes.map fun row => row.2.1)
  checkUniqueNames "supervision shape" (supervisionShapes.map Prod.fst)
  unless supervisionOwned.length == 705 && supervisionApi.length == 294 &&
      supervisionTheorems.length == 136 && supervisionTypes.length == 27 &&
      supervisionShapes.length == 19 && supervisionLeaves.length == 3 do
    failJoin "supervision frozen census counts drifted"
  checkOwners owner (supervisionApi.map Prod.fst)
  for (name, route) in supervisionApi do
    unless route == supervisionRoute name do
      failJoin m!"supervision declaration route drifted: {name}"
  let api := supervisionApi.map Prod.fst
  unless (supervisionTheorems.map Prod.fst).all api.contains &&
      (supervisionTypes.map fun row => row.2.1).all api.contains do
    failJoin "supervision receipt absent from authored API"
  for (name, expected, _) in supervisionTheorems do
    match (← getEnv).find? name with
    | some (.thmInfo _) => pure ()
    | _ => failJoin m!"supervision law {name} is not a theorem declaration"
    let actual ← canonicalAxiomText name
    unless actual == expected do
      failJoin m!"supervision axiom receipt for {name}: expected {expected}, found {actual}"
  for (name, constructors, fields) in supervisionShapes do
    checkSupervisionShape name constructors fields
  checkUniqueStrings "supervision leaf" (supervisionLeaves.map Prod.fst)
  for (_, name, receipt) in supervisionLeaves do
    unless (supervisionShapes.map Prod.fst).contains name &&
        (supervisionTheorems.map Prod.fst).contains receipt do
      failJoin m!"supervision leaf lacks shape or theorem: {name}"
  checkUniqueStrings "supervision graph edge" (supervisionEdges.map Prod.fst)
  unless supervisionEdges.map Prod.fst ==
      ["IDENTITY", "CONSTRUCTION", "SEMANTICS", "LAWS", "REPRESENTATION",
       "COUNTEREXAMPLES", "BRIDGES", "TARGETS", "TRUST", "COVERAGE"] do
    failJoin "supervision graph needs the exact ten frozen edges in order"
  for (edge, _, state) in supervisionEdges do
    let expected := if edge == "REPRESENTATION" then "not-applicable"
      else if edge == "BRIDGES" || edge == "TARGETS" || edge == "TRUST" then "required-open"
      else "required-local"
    unless state == expected do
      failJoin m!"supervision graph boundary was relabeled: {edge}"

private def emitSupervisionAssurance : CommandElabM Unit := do
  checkSupervisionAssurance
  for name in supervisionOwned do
    liftIO <| IO.println s!"E4SUP\towned-declaration\t{name}\tEffect4.Concurrency.Supervision\t{supervisionRoute name}"
  for (name, route) in supervisionApi do
    liftIO <| IO.println s!"E4SUP\tapi\t{name}\tEffect4.Concurrency.Supervision\t{route}"
  for (name, expected, rows) in supervisionTheorems do
    liftIO <| IO.println s!"E4SUP\ttheorem\t{name}\t{supervisionRoute name}\t{rows}"
    liftIO <| IO.println s!"E4SUP\taxiom\t{name}\t{expected}\tSUPERVISION-AXIOM-RECEIPT"
  for (id, name, relationship, route) in supervisionTypes do
    liftIO <| IO.println s!"E4SUP\ttype\t{id}\t{name}\tEffect4.Concurrency.Supervision\t{relationship}\t{route}"
  for (name, constructors, fields) in supervisionShapes do
    let ctorText := String.intercalate "," (constructors.map Name.toString)
    let fieldText := match fields with
      | none => "inductive"
      | some names => String.intercalate "," (names.map Name.toString)
    liftIO <| IO.println s!"E4SUP\tshape\t{name}\t{ctorText}\t{fieldText}"
  for (id, name, receipt) in supervisionLeaves do
    liftIO <| IO.println s!"E4SUP\tleaf-receipt\t{id}\t{name}\tSUPERVISION-PG-RC112/CONSTRUCTION\t{receipt}"
  for (edge, evidence, state) in supervisionEdges do
    liftIO <| IO.println s!"E4SUP\tgraph-edge\tSUPERVISION-PG-RC112/{edge}\t{evidence}\t{state}"

syntax (name := effect4CheckSupervisionShape)
  "#effect4_check_supervision_shape " ident "[" ident,* "]" "[" ident,* "]" : command

elab_rules : command
  | `(#effect4_check_supervision_shape $name:ident [$ctors:ident,*] [$fields:ident,*]) =>
      checkSupervisionShape name.getId (ctors.getElems.map Syntax.getId).toList
        (some (fields.getElems.map Syntax.getId).toList)

syntax (name := effect4EmitSupervisionAssurance) "#effect4_emit_supervision_assurance" : command
elab_rules : command
  | `(#effect4_emit_supervision_assurance) => emitSupervisionAssurance

#effect4_emit_supervision_assurance

end Effect4Test.Concurrency.FiberAssurance
