import Lean
import Lean.Util.CollectAxioms
import Effect4.Concurrency.Scheduler

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

end Effect4Test.Concurrency.FiberAssurance
