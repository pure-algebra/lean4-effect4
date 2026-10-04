import Effect4.Api.HostProtocol
import Effect4.Laws.Auto.Inversion
import Effect4.Laws.Auto.Semantics

/-! P2b observation laws. Host waits take priority over aggregate exit and
runnable observations. Driver completion is not inferred from these predicates.
R12-b closes the module: the tape frontier is empty exactly at a deadlock. -/
set_option autoImplicit false
namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program
/-- Work inspection's runnable-ID reader names exactly a live unparked recorded fiber.
This is the membership helper for Run's `run-work-selection` claim, not progress. -/
theorem mem_runnableFibers (m : NativeMachine) (id : FiberId) :
    id ∈ runnableFibers m ↔
      ∃ f ∈ m.fibers, f.id = id ∧ f.exit.isNone = true ∧ f.parked = .notParked := by
  simp only [runnableFibers, List.mem_map, List.mem_filter, isRunnable,
    Bool.and_eq_true, beq_iff_eq]
  aesop

theorem awaitHost_mem (why : Exhaustion) (m : NativeMachine) (key : HostProtocol.Key) :
    .awaitHost key ∈ frontierReasons why m ↔ .awaitHost key ∈ hostReasons m := by
  cases why <;> cases h : hasRunnable m <;>
    simp [frontierReasons, h, compileReasons, timerReasons]

/-- The decision reason is present exactly at a tape frontier with a runnable fiber or an
armed owner (decisions row 201 (b)). -/
theorem awaitDecision_iff (why : Exhaustion) (m : NativeMachine) :
    .awaitDecision ∈ frontierReasons why m ↔
      why = .tape ∧ (hasRunnable m = true ∨ m.armed ≠ []) := by
  cases why <;> aesop (add norm simp [frontierReasons, compileReasons, hostReasons, timerReasons])

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
    cases hr : hasRunnable m <;> simp

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
    cases hr : hasRunnable m <;> simp

theorem observe_idle_iff (why : Exhaustion) (m : NativeMachine) :
    HostProtocol.observe m = .idle ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧ hasRunnable m = true := by
  rw [exists_awaitHost_iff]
  change (if !(Program.awaits m).isEmpty then HostProtocol.State.awaitingAsync
    else if m.fibers.all (fun f => f.exit.isSome) then .terminated
    else if hasRunnable m then .idle else .parked) = _ ↔ _
  cases ha : (Program.awaits m).isEmpty <;>
    cases he : m.fibers.all (fun f => f.exit.isSome) <;>
    simp
  exact all_exited_not_runnable m he

/-- DI-68's tape law, as decisions row 201 (b) amends it: with no host wait at a tape frontier,
the decision reason is present exactly when the observer reads `idle` or an owner is armed. An
armed owner with no runnable fiber reads `parked` (`E4-SCHED-CE-021`). -/
theorem observe_idle_tape_iff (m : NativeMachine)
    (h : ¬ ∃ key, .awaitHost key ∈ frontierReasons .tape m) :
    (HostProtocol.observe m = .idle ∨ m.armed ≠ []) ↔
      .awaitDecision ∈ frontierReasons .tape m := by
  rw [observe_idle_iff .tape, awaitDecision_iff]
  simp only [h, not_false_eq_true, true_and, ne_eq]

/-- The observation and reason alphabet agree, with host priority explicit. -/
theorem observe_of_reasons (why : Exhaustion) (m : NativeMachine) :
    (HostProtocol.observe m = .awaitingAsync ↔ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧
    (HostProtocol.observe m = .terminated ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧
      m.fibers.all (fun f => f.exit.isSome) = true) ∧
    (HostProtocol.observe m = .idle ↔
      (¬ ∃ key, .awaitHost key ∈ frontierReasons why m) ∧ hasRunnable m = true) ∧
    (.awaitDecision ∈ frontierReasons why m ↔
      why = .tape ∧ (hasRunnable m = true ∨ m.armed ≠ [])) :=
  ⟨observe_awaitingAsync_iff why m, observe_terminated_iff why m,
    observe_idle_iff why m, awaitDecision_iff why m⟩

/-! ## R12-b: an empty frontier is a deadlock

R12 (`docs/core/system-map.md` §8) asks that `Deadlocked` require nothing armed. -/

/-- **A deadlocked machine** (R12): live and unfinished, with nothing to wait for, read in the
frontier's order. No fiber's current code stands at its compile budget, no fiber awaits a host
reply, no fiber sleeps on a timer, no fiber is runnable, and no owner is armed. -/
def Deadlocked (m : NativeMachine) : Prop :=
  m.stuck = none ∧ m.finished = false ∧
    (∀ f ∈ m.fibers, isCompileFrontier f.frame.current = false) ∧ Program.awaits m = [] ∧
    m.state.timers.wake.waiters = [] ∧ hasRunnable m = false ∧ m.armed = []

/-- **R12-b: at a live, unfinished machine, the tape frontier is empty exactly at a deadlock.**
So the frontier names a reason whenever work is armed (`E4-SCHED-CE-021`, repaired by decisions
row 201 (b)).

Concept `reactive-scheduling`, claim `frontier-names-work`: the frontier half of the
classification that `scheduler-progress` asks for. Reach: every frame machine (`NativeMachine`),
with no reachability or typing premise, at the tape exhaustion site; a fuel frontier always names
`.commandFuel` (`commandFuel_iff`). It does not establish that the named decision steps the
machine, what any decision does at a deadlocked machine, or liveness (R12-c). It serves R12:
`Deadlocked` requires nothing armed. -/
@[semantics "reactive-scheduling"]
theorem frontier_empty_iff_deadlocked (m : NativeMachine) (live : m.stuck = none)
    (unfinished : m.finished = false) :
    frontierReasons .tape m = [] ↔ Deadlocked m := by
  aesop (add norm simp [frontierReasons, Deadlocked, compileReasons, hostReasons, timerReasons,
    List.filterMap_eq_nil_iff])
end Effect4.Api
