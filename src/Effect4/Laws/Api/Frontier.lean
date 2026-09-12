import Effect4.Api.HostProtocol

/-! P2b observation laws. Host waits take priority over aggregate exit and
runnable observations. Driver completion is not inferred from these predicates. -/
set_option autoImplicit false
namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program
theorem awaitHost_mem (why : Exhaustion) (m : NativeMachine) (key : HostProtocol.Key) :
    .awaitHost key ∈ frontierReasons why m ↔ .awaitHost key ∈ hostReasons m := by
  cases why <;> cases h : hasRunnable m <;>
    simp [frontierReasons, h, compileReasons, timerReasons]

theorem awaitDecision_iff (why : Exhaustion) (m : NativeMachine) :
    .awaitDecision ∈ frontierReasons why m ↔ why = .tape ∧ hasRunnable m = true := by
  cases why <;> cases h : hasRunnable m <;>
    simp [frontierReasons, h, compileReasons, hostReasons, timerReasons]

theorem commandFuel_iff (why : Exhaustion) (m : NativeMachine) :
    .commandFuel ∈ frontierReasons why m ↔ why = .fuel := by
  cases why <;> cases h : hasRunnable m <;>
    simp [frontierReasons, h, compileReasons, hostReasons, timerReasons]

theorem exists_awaitHost_iff (why : Exhaustion) (m : NativeMachine) :
    (∃ key, .awaitHost key ∈ frontierReasons why m) ↔ (Program.awaits m).isEmpty = false := by
  simp only [awaitHost_mem]
  cases h : Program.awaits m with
  | nil => simp [hostReasons, h]
  | cons a rest =>
    rcases a with ⟨fiber, token, op, request⟩
    simp [hostReasons, h]

theorem all_exited_not_runnable (m : NativeMachine)
    (h : m.fibers.all (fun f => f.exit.isSome) = true) : hasRunnable m = false := by
  apply Bool.eq_false_iff.mpr
  intro hr
  obtain ⟨f, hf, hr⟩ := List.any_eq_true.mp hr
  have he := List.all_eq_true.mp h f hf
  cases hx : f.exit <;> simp_all

theorem observe_awaitingAsync_iff (why : Exhaustion) (m : NativeMachine) :
    HostProtocol.observe m = .awaitingAsync ↔ ∃ key, .awaitHost key ∈ frontierReasons why m := by
  rw [exists_awaitHost_iff]
  change (if !(Program.awaits m).isEmpty then HostProtocol.State.awaitingAsync
    else if m.fibers.all (fun f => f.exit.isSome) then .terminated
    else if hasRunnable m then .idle else .parked) = _ ↔ _
  cases h : (Program.awaits m).isEmpty <;>
    cases he : m.fibers.all (fun f => f.exit.isSome) <;>
    cases hr : hasRunnable m <;> simp [h, he, hr]

theorem observe_terminated_iff (why : Exhaustion) (m : NativeMachine) :
    HostProtocol.observe m = .terminated ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧
      m.fibers.all (fun f => f.exit.isSome) = true := by
  rw [exists_awaitHost_iff]
  change (if !(Program.awaits m).isEmpty then HostProtocol.State.awaitingAsync
    else if m.fibers.all (fun f => f.exit.isSome) then .terminated
    else if hasRunnable m then .idle else .parked) = _ ↔ _
  cases ha : (Program.awaits m).isEmpty <;>
    cases he : m.fibers.all (fun f => f.exit.isSome) <;>
    cases hr : hasRunnable m <;> simp [ha, he, hr]

theorem observe_idle_iff (why : Exhaustion) (m : NativeMachine) :
    HostProtocol.observe m = .idle ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧ hasRunnable m = true := by
  rw [exists_awaitHost_iff]
  change (if !(Program.awaits m).isEmpty then HostProtocol.State.awaitingAsync
    else if m.fibers.all (fun f => f.exit.isSome) then .terminated
    else if hasRunnable m then .idle else .parked) = _ ↔ _
  cases ha : (Program.awaits m).isEmpty <;>
    cases he : m.fibers.all (fun f => f.exit.isSome) <;>
    simp [ha, he]
  exact all_exited_not_runnable m he

theorem observe_idle_tape_iff (m : NativeMachine)
    (h : ¬ ∃ key, .awaitHost key ∈ frontierReasons .tape m) :
    HostProtocol.observe m = .idle ↔ .awaitDecision ∈ frontierReasons .tape m := by
  rw [observe_idle_iff .tape, awaitDecision_iff]
  simp [h]


/-- The observation and reason alphabet agree, with host priority explicit. -/
theorem observe_of_reasons (why : Exhaustion) (m : NativeMachine) :
    (HostProtocol.observe m = .awaitingAsync ↔ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧
    (HostProtocol.observe m = .terminated ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧
      m.fibers.all (fun f => f.exit.isSome) = true) ∧
    (HostProtocol.observe m = .idle ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧ hasRunnable m = true) ∧
    (.awaitDecision ∈ frontierReasons why m ↔ why = .tape ∧ hasRunnable m = true) :=
  ⟨observe_awaitingAsync_iff why m, observe_terminated_iff why m,
    observe_idle_iff why m, awaitDecision_iff why m⟩
end Effect4.Api
