import Test.Dogfood.Proofs.HostTimeoutNumberFlow
import Test.Dogfood.Proofs.HostTimeoutNumberPhase

/-!
Concept: scope-lifetime-finalization R11.
Question: cancellation awaits the actual attempt cleanup before a completed form can publish.
Consumer: the numeric countdown command and its saved reply assertion for Timeout.cleanup_keeps.
Reach: actual countdown walks and their looked-up attempt fiber.
Limit: the attempt-exit assertion remains an input from the numeric configuration.
The countdown walk supplies completion, not the cleanup writer's source permission.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutNumberWait
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberFlow

/-- An active attempt's heap is distinct from every heap containing its completed cleanup. -/
theorem active_not_cleaned (image : Image) (own : image.count = image.cleanups.length + 1)
    (exit : ExitV) : image.heap ≠ (image.cleanup own exit).heap := by
  intro equal
  have cell := congrArg (fun (heap : RefHeap) => heap[1]?) equal
  change some (Val.list image.cleanups) =
    some (Val.list (image.cleanups ++ [.list [.nat image.count, .bool (HostTimeoutNumberSteps.interruptionFlag exit)]])) at cell
  have logs := congrArg Store.Val.children (Option.some.inj cell)
  change image.cleanups = image.cleanups ++ [.list [.nat image.count, .bool (HostTimeoutNumberSteps.interruptionFlag exit)]] at logs
  have lengths := congrArg List.length logs
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at lengths
  omega

/-- A completed actual countdown has seen an exit for every target that the machine holds. -/
theorem countdown_complete (machine : Effect4.Program.NativeMachine) (targets : List FiberId)
    (collected : List ExitV) (complete : (countdownWalk machine targets collected).2 = none)
    (id : FiberId) (member : id ∈ targets) (fiber : Effect4.Program.SourceScope.SourceFiber)
    (found : machine.fiber? id = some fiber) : fiber.exit.isSome = true := by
  induction targets generalizing collected with
  | nil => cases member
  | cons head rest ih =>
    cases selected : machine.fiber? head with
    | none =>
      have different : id ≠ head := by
        intro equal
        rw [equal, selected] at found
        cases found
      have tail : id ∈ rest := (List.mem_cons.mp member).resolve_left different
      exact ih collected (by simpa only [countdownWalk, selected] using complete) tail
    | some target =>
      cases exited : target.exit with
      | none =>
        simp only [countdownWalk, selected, exited] at complete
        cases complete
      | some exit =>
        rcases List.mem_cons.mp member with equal | tail
        · rw [equal, selected] at found
          cases found
          rw [exited]
          rfl
        · exact ih (collected ++ [exit])
            (by simpa only [countdownWalk, selected, exited] using complete) tail

/-- An active attempt's published exit certifies its own completed cleanup at the current heap. -/
structure AttemptExitAt (image : Image) (own : image.count = image.cleanups.length + 1)
    (machine : Effect4.Program.NativeMachine) (attempt : FiberId) : Prop where
  held : ∃ fiber, machine.fiber? attempt = some fiber
  cleaned : ∀ fiber, machine.fiber? attempt = some fiber → fiber.exit.isSome = true →
    ∃ exit, ImageAt (image.cleanup own exit) machine.state

/-- The numeric stored exit class supplies the cancellation wait's concrete attempt assertion. -/
theorem attempt_exit_at (image : Image) (own : image.count = image.cleanups.length + 1)
    (machine : Effect4.Program.NativeMachine) (attempt : FiberId)
    (held : ∃ fiber, machine.fiber? attempt = some fiber)
    (exits : ∀ fiber, machine.fiber? attempt = some fiber → ∀ exit, fiber.exit = some exit →
      AnswerFlow.ExitAt (model machine.completedExits) machine.state (.cleanupExit image own) exit) :
    AttemptExitAt image own machine attempt := by
  refine ⟨held, ?_⟩
  intro fiber found published
  cases returned : fiber.exit with
  | none => rw [returned] at published; cases published
  | some exit =>
    have classified := exits fiber found exit returned
    cases exit with
    | success value => exact classified
    | failure cause => exact classified

/-- The cancellation wait either already has cleanup or actually awaits its owning attempt. -/
def AwaitAt (image : Image) (own : image.count = image.cleanups.length + 1)
    (machine : Effect4.Program.NativeMachine) (targets : List FiberId) : Prop :=
  (∃ exit, ImageAt (image.cleanup own exit) machine.state) ∨
    ∃ attempt, attempt ∈ targets ∧ AttemptExitAt image own machine attempt

/-- A completed cancellation countdown supplies the exact post-cleanup heap to the saved form. -/
theorem await_cleaned (image : Image) (own : image.count = image.cleanups.length + 1)
    (machine : Effect4.Program.NativeMachine) (targets : List FiberId) (collected : List ExitV)
    (awaiting : AwaitAt image own machine targets)
    (complete : (countdownWalk machine targets collected).2 = none) :
    ∃ exit, ImageAt (image.cleanup own exit) machine.state := by
  rcases awaiting with cleaned | ⟨attempt, member, active⟩
  · exact cleaned
  · obtain ⟨fiber, found⟩ := active.held
    exact active.cleaned fiber found (countdown_complete machine targets collected complete attempt member fiber found)

/-- The actual countdown cannot take its completed arm while the owning cleanup is still absent. -/
theorem await_pending (image : Image) (own : image.count = image.cleanups.length + 1)
    (machine : Effect4.Program.NativeMachine) (targets : List FiberId) (collected : List ExitV)
    (awaiting : AwaitAt image own machine targets) (active : ImageAt image machine.state) :
    (countdownWalk machine targets collected).2 ≠ none := by
  intro complete
  obtain ⟨exit, cleaned⟩ := await_cleaned image own machine targets collected awaiting complete
  exact active_not_cleaned image own exit (active.symm.trans cleaned)

/-- Minting a guard changes no fiber inspected by the actual countdown walk. -/
theorem countdown_token (machine : Effect4.Program.NativeMachine) (token : Nat) (targets : List FiberId)
    (collected : List ExitV) :
    countdownWalk {machine with nextToken := token} targets collected =
      countdownWalk machine targets collected := by
  induction targets generalizing collected with
  | nil => rfl
  | cons head rest ih =>
    simp only [countdownWalk]
    rw [show ({machine with nextToken := token} : Effect4.Program.NativeMachine).fiber? head =
      machine.fiber? head from rfl]
    cases found : machine.fiber? head with
    | none => exact ih collected
    | some fiber =>
      dsimp only
      cases exited : fiber.exit with
      | none => rfl
      | some exit => exact ih (collected ++ [exit])

/-- The real cancellation wait parks at its fresh guard while the cleanup is still absent. -/
theorem countdown_waits (image : Image) (own : image.count = image.cleanups.length + 1)
    (machine : Effect4.Program.NativeMachine) (fiber : Effect4.Program.SourceScope.SourceFiber)
    (targets : List FiberId) (awaiting : AwaitAt image own machine targets)
    (active : ImageAt image machine.state) :
    (countdownParkEdits (HostTimeoutFlow.interpreter machine.completedExits) machine fiber targets
      .exitsValue).2.1.parked = .withGuard machine.nextToken := by
  have pending := await_pending image own machine targets [] awaiting active
  unfold countdownParkEdits
  dsimp only
  rw [countdown_token]
  cases walked : countdownWalk machine targets [] with
  | mk exits next =>
    cases next with
    | none => exact False.elim (pending (congrArg Prod.snd walked))
    | some target => rfl

end Test.Dogfood.Proofs.HostTimeoutNumberWait
