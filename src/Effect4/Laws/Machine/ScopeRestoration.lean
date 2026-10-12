import Effect4.Laws.Machine.ScopeMachine
import Effect4.Machine.Frames

/-!
# Scope cleanup resumed through the frame machine

Owner: the local ScopeMachine-to-FrameFiber connection frozen by
`Test/contracts/scope-restoration.contract.md` at `945f729`.
The only executable adapter maps the existing completed restored exit through
existing `FrameFiber.step`; it adds no carrier, evaluator, source runner or
interruption policy. Existing ScopeMachine owns actual cleanup execution and
its retained service state, while Runtime owns continuation and mask behavior.

The nine public equations retain the complete frame step/events and state.
The mask-arm equations name the precise top frame and false deferred latch;
completion itself admits arbitrary fibers. A successful restored exit can
become pending interruption immediately; a failing exit follows the real
failure-arm skip through the remaining continuation. The recorded substituted
event observes the hook even when its replacement is skipped.

Scope/Frame/D4 graph connections are recorded in `docs/research/SCOPE-DAG.md` and
`docs/research/TRACE-DAG.md`. This local composition does not establish general region
compilation, arbitrary finalizer-program execution, scheduling, interrupt-tape
lowering, or host equivalence. The separate 40-case host probe is finite
source-pinned evidence, with fallible-release and legal-defect cases labelled.
-/

namespace Effect4.ScopeRestoration
open Effect4
universe u v
variable {κ φ ν τ : Type u} {β : Type v} {ε δ ι α σ : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Resume only completed cleanup through the existing frame step, retaining its full events. -/
def resumeClosedScope (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α) (fiber : FrameFiber ν τ β ε δ ι α) :
    Option (FrameStep ν τ β ε δ ι α × List (FrameEvent ν τ β ε δ ι α)) :=
  (ScopeMachine.restore? machine).map fun exit =>
    FrameFiber.step interp { fiber with current := Prim.ofExit exit }

/-- An unfinished close supplies no frame step and leaves its residual available to its caller. -/
theorem resumeClosedScope_unfinished (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α) (fiber : FrameFiber ν τ β ε δ ι α)
    (phase : machine.phase ≠ .complete) : resumeClosedScope interp machine fiber = none := by
  unfold resumeClosedScope ScopeMachine.restore? ScopeMachine.result?
  cases actual : machine.phase with
  | ready | waiting operation => rfl
  | complete => exact False.elim (phase actual)

/-- Successful cleanup restores pending interruption before touching the arbitrary outer continuation. census: op.SetInterruptible -/
theorem resumeClosedScope_success_pending (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α) (current : Prim ν τ β ε δ ι α)
    (rest : List (Prim ν τ β ε δ ι α)) (value : β) (pending : Cause ε δ ι α)
    (completed : ScopeMachine.restore? machine = some (.success value)) :
    resumeClosedScope interp machine ⟨current, .setInterruptible true :: rest, false, some pending, false⟩ =
      some (.running ⟨.failure pending, rest, true, some pending, false⟩,
        [.popped (.setInterruptible true), .ranContAll (.setInterruptible true), .substituted pending]) := by
  simp [resumeClosedScope, completed, Prim.ofExit, FrameFiber.step, FrameFiber.resumeValue,
    FrameFiber.getCont, FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.passEvents,
    Prim.hasArm, Prim.arms]

/-- A walk that starts with a carried cause ends with one: a skip only changes the cause it
carries. A step of `resumeClosedScope_failure_pending`, whose resumed failure is read through
the carried cause. -/
theorem popFrom_carriedCause_isSome (demand : Arm) (skip : Bool)
    (frames : List (Prim ν τ β ε δ ι α)) (fiber : FrameFiber ν τ β ε δ ι α)
    (cause : Option (Cause ε δ ι α)) :
    (FrameFiber.popFrom demand skip frames fiber cause).carriedCause.isSome = cause.isSome := by
  have skipped : ∀ (frame : Prim ν τ β ε δ ι α) (f : FrameFiber ν τ β ε δ ι α)
      (c : Option (Cause ε δ ι α)), (FrameFiber.skippedCause demand frame f c).isSome = c.isSome := by
    intro frame f c
    cases c with
    | none => rfl
    | some c =>
      simp only [FrameFiber.skippedCause]
      split
      · split <;> rfl
      · rfl
  have pushed : ∀ (f : FrameFiber ν τ β ε δ ι α) (c : Option (Cause ε δ ι α)),
      (FrameFiber.passPushed demand skip f c).carriedCause.isSome = c.isSome := by
    intro f c
    unfold FrameFiber.passPushed
    split
    · rfl
    · dsimp only
      split
      · split
        · exact skipped _ _ _
        · rfl
      · rfl
  induction frames generalizing fiber cause with
  | nil => rfl
  | cons frame rest ih =>
    simp only [FrameFiber.popFrom]
    split
    · split
      · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
        split <;> simp only [ih, pushed, skipped]
      · rfl
    · simp only [FrameFiber.passOn, FrameFiber.joinPushed]
      split <;> simp only [ih, pushed]

/-- The failure arm skips the restoration replacement. Latest's walk adds the recorded interrupt
to the failure it carries (Effect 4.0.1 `internal/core.ts:580-608`; signed divergence U-01 from
rc.112, which passes the failure unchanged), and the actual tail resumes that failure.
`FrameFiber.resumeCause` reads no current primitive. census: checkpoint.exit-failcause-skip -/
theorem resumeClosedScope_failure_pending (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α) (current : Prim ν τ β ε δ ι α)
    (rest : List (Prim ν τ β ε δ ι α)) (failed pending : Cause ε δ ι α)
    (completed : ScopeMachine.restore? machine = some (.failure failed)) :
    resumeClosedScope interp machine ⟨current, .setInterruptible true :: rest, false, some pending, false⟩ =
      let continued := (⟨.failure failed, rest, true, some pending, false⟩ :
        FrameFiber ν τ β ε δ ι α).resumeCause interp (Cause.combine failed pending)
          (some (.failure (Cause.combine failed pending)))
      some (continued.1,
        [.popped (.setInterruptible true), .ranContAll (.setInterruptible true), .substituted pending]
          ++ continued.2) := by
  let tail : FrameFiber ν τ β ε δ ι α :=
    ⟨.failure failed, rest, true, some pending, false⟩
  have hpop :
      (⟨.failure failed, .setInterruptible true :: rest, false, some pending, false⟩ :
        FrameFiber ν τ β ε δ ι α).getCont .contE true (some failed) =
      FrameFiber.passOn (.setInterruptible true) (some (.failure pending))
        (tail.getCont .contE true (some (Cause.combine failed pending))) := by rfl
  have hsome := popFrom_carriedCause_isSome .contE true rest
    ⟨.failure failed, [], true, some pending, false⟩ (some (Cause.combine failed pending))
  obtain ⟨carried, hcarried⟩ : ∃ carried,
      (tail.getCont .contE true (some (Cause.combine failed pending))).carriedCause = some carried := by
    cases he : (tail.getCont .contE true (some (Cause.combine failed pending))).carriedCause with
    | none =>
      change (FrameFiber.popFrom .contE true rest ⟨.failure failed, [], true, some pending, false⟩
        (some (Cause.combine failed pending))).carriedCause = none at he
      rw [he] at hsome
      cases hsome
    | some carried => exact ⟨carried, rfl⟩
  dsimp only [resumeClosedScope]
  rw [completed]
  change some ((⟨.failure failed, .setInterruptible true :: rest, false, some pending, false⟩ :
    FrameFiber ν τ β ε δ ι α).resumeCause interp failed (some (.failure failed))) =
    let continued := tail.resumeCause interp (Cause.combine failed pending)
      (some (.failure (Cause.combine failed pending)))
    some (continued.1,
      [.popped (.setInterruptible true), .ranContAll (.setInterruptible true), .substituted pending]
        ++ continued.2)
  simp only [FrameFiber.resumeCause, hpop, FrameFiber.passOn, Prim.passEvents,
    Prim.hasArm, Prim.arms, Option.map_some, Option.getD_some, FramePop.deliveredExit, hcarried,
    show [Arm.contAll].contains Arm.contAll = true from rfl, if_true]
  split
  · rfl
  · rfl
  · rfl
  · split <;> simp only [List.append_assoc]

/-- The actual stateful close and adapter agree with existing closeExitsM, exact restoration and the real frame step. census: scope.close-sequential -/
theorem resumeClosedScope_complete
    (interp : PrimInterp ν τ β ε δ ι α)
    (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
    (scope : Scope κ φ β ε δ ι α) (original : Exit β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α) (world : σ) :
    (let actual := ScopeMachine.runState handler (ScopeMachine.bound scope)
       (ScopeMachine.start scope original) world
     (resumeClosedScope interp actual.1 fiber, actual.2)) =
    (let completed := (Scope.closeExitsM handler scope original).run world
     let cleanup := match completed.1 with
       | [] => Exit.void
       | [only] => only
       | first :: second :: rest => Exit.asVoidAll (first :: second :: rest)
     (some (FrameFiber.step interp
       { fiber with current := Prim.ofExit (Exit.restoreAfterFinalizer original cleanup) }),
      completed.2)) := by
  exact congrArg (fun pair : Option (Exit β ε δ ι α) × σ =>
      (pair.1.map (fun exit => FrameFiber.step interp { fiber with current := Prim.ofExit exit }), pair.2))
    (ScopeMachine.runState_restore handler scope original world)

/-- Without a pending cause, successful restoration continues through the actual outer frames. census: op.SetInterruptible -/
theorem resumeClosedScope_success_no_pending
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current : Prim ν τ β ε δ ι α) (rest : List (Prim ν τ β ε δ ι α))
    (value : β)
    (completed : ScopeMachine.restore? machine = some (.success value)) :
    resumeClosedScope interp machine
      ⟨current, .setInterruptible true :: rest, false, none, false⟩ =
    (let continued := FrameFiber.step interp ⟨.success value, rest, true, none, false⟩
     some (continued.1,
       [.popped (.setInterruptible true), .ranContAll (.setInterruptible true)]
        ++ continued.2)) := by
  simp [resumeClosedScope, completed, Prim.ofExit, FrameFiber.step, FrameFiber.resumeValue,
    FrameFiber.getCont, FrameFiber.popFrom, FrameFiber.joinPushed,
    FrameFiber.passPushed, FrameFiber.passOn, Prim.ensure, Prim.answerOf, Prim.passEvents,
    Prim.hasArm, Prim.arms, List.append_assoc]
  split <;> (try simp_all) <;> (split <;> simp_all)

/-- Nested uninterruptible adds no restoring frame when an outer mask remains active. census: scope.acquire-release -/
theorem resumeClosedScope_already_masked
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α)
    (masked : fiber.interruptible = false) :
    resumeClosedScope interp machine fiber.uninterruptible =
      resumeClosedScope interp machine fiber := by
  rw [FrameFiber.uninterruptible_already_masked fiber masked]

/-- A successful inner close takes its actual value continuation while retaining the outer mask and pending cause. census: op.Success -/
theorem resumeClosedScope_masked_continuation
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current body : Prim ν τ β ε δ ι α)
    (continuation : ν) (rest : List (Prim ν τ β ε δ ι α))
    (value : β) (pending : Option (Cause ε δ ι α))
    (completed : ScopeMachine.restore? machine = some (.success value)) :
    resumeClosedScope interp machine
      ⟨current, .onSuccess body continuation :: rest, false, pending, false⟩ =
    some (.running ⟨interp.contA continuation value, rest, false, pending, false⟩,
      [.popped (.onSuccess body continuation)]) := by
  simp [resumeClosedScope, completed, Prim.ofExit, FrameFiber.step, FrameFiber.resumeValue,
    FrameFiber.getCont, FrameFiber.popFrom, Prim.ensure, Prim.answerOf, Prim.passEvents,
    Prim.hasArm, Prim.arms, Prim.armA, Prim.finalizerEvents]

/-- An original failure and cleanup failure enter Runtime through existing Cause.combine. census: cause.finalizer-merge -/
theorem resumeClosedScope_failure_cleanup
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (fiber : FrameFiber ν τ β ε δ ι α)
    (failed cleanup : Cause ε δ ι α)
    (original : machine.original = .failure failed)
    (completed : ScopeMachine.result? machine = some (.failure cleanup)) :
    resumeClosedScope interp machine fiber =
    some (FrameFiber.step interp
      { fiber with current := .failure (Cause.combine failed cleanup) }) := by
  simp [resumeClosedScope, ScopeMachine.restore?, completed, original,
    Exit.restoreAfterFinalizer, Exit.mergeFinalizer, Prim.ofExit]

/-- Cleanup failure follows the failure-restoration path even when interruption is pending: the
tail resumes the cleanup failure with the pending cause added (latest's walk; U-01), so the
pending interrupt never replaces it. census: checkpoint.exit-failcause-skip -/
theorem resumeClosedScope_success_cleanup_failure
    (interp : PrimInterp ν τ β ε δ ι α)
    (machine : ScopeMachine.State κ φ β ε δ ι α)
    (current : Prim ν τ β ε δ ι α) (rest : List (Prim ν τ β ε δ ι α))
    (value : β) (cleanup pending : Cause ε δ ι α)
    (original : machine.original = .success value)
    (completed : ScopeMachine.result? machine = some (.failure cleanup)) :
    resumeClosedScope interp machine
      ⟨current, .setInterruptible true :: rest, false, some pending, false⟩ =
    (let continued := (⟨.failure cleanup, rest, true, some pending, false⟩ :
       FrameFiber ν τ β ε δ ι α).resumeCause interp (Cause.combine cleanup pending)
         (some (.failure (Cause.combine cleanup pending)))
     some (continued.1,
       [.popped (.setInterruptible true), .ranContAll (.setInterruptible true),
        .substituted pending] ++ continued.2)) := by
  apply resumeClosedScope_failure_pending
  simp [ScopeMachine.restore?, completed, original, Exit.restoreAfterFinalizer, Exit.mergeFinalizer]

end Effect4.ScopeRestoration
