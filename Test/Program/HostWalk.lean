import Test.Program.RegistrationYield
import Effect4.Laws.Program.Typed.HostWalk

/-!
# Test.Program.HostWalk — the walk over a host stack reaches its new outcomes

Placement: semantics Concept 4, the walk consumer of `M6Ledger.step_loop` and `.step_deliver`
(`popR_hostTyped`, `Typed/HostWalk.lean`). Two stacks from RegistrationYield's fixtures, each
delivered a typed success under the reference interpreter's hook laws at the fixture's world. Two
registration arrows: the first installs its race's marker over the second (the `HostMarker`
outcome, the case the ordinary walk has no outcome for). An answer slot above an arrow: the
ordinary slot completes (`popR_cons`'s second branch) and the arrow then installs the marker.

Reach: finite stacks at one world; the controls show the theorem's new outcome is inhabited and
that its other outcomes are excluded there. They do not exercise the machine's interpreter
(`interpRAt`, whose hook laws are G2) or a whole step.
-/

set_option autoImplicit false

namespace Test.Program.HostWalkControls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
open Test.Program.RegistrationYield (rootProgram natTy world marker yieldNext yieldCurrent iaNext
  iaSlot arrow fiberOf machineOf provenance marker_not_typed)

theorem unit_ok : ExitOk world (EffTy.pure .unit) (.success Val.unit) :=
  ⟨by rw [fitsExit_success_iff]; exact trivial, trivial⟩

/-- A walk outcome whose current code is the race's marker is the marker outcome. -/
theorem marker_outcome {m : RState} {tout : EffTy} {x : RSaved} (current : x.current = marker)
    (h : HostWalkTyped (rootProgram : ProgramSource) world m Api.root tout (x, none)) :
    HostMarker (rootProgram : ProgramSource) world m Api.root tout x := by
  rcases h with ⟨tin, code, _, _⟩ | ⟨_, _, _, _, callback, _⟩ | marked
  · rw [current] at code
    exact absurd code (marker_not_typed world tin)
  · rw [current] at callback
    cases callback
  · exact marked

namespace Double

def stack : List ScopeFrame := [.resume .onSuccess yieldNext, .resume .onSuccess yieldNext]
def fiber : RFiber := fiberOf yieldCurrent stack 1

theorem host : HostStack (rootProgram : ProgramSource) world (machineOf fiber) Api.root
    (EffTy.pure .unit) natTy stack :=
  arrow rfl rfl (arrow rfl rfl (.nil natTy))

/-- The actual walk installs the marker over the second arrow. -/
theorem walk_eq : popR (interpR rootProgram) (.success Val.unit) stack fiber.frame =
    ({ fiber.frame with current := marker, stack := [.resume .onSuccess yieldNext] }, none) := rfl

theorem reaches_marker :
    HostMarker (rootProgram : ProgramSource) world (machineOf fiber) Api.root natTy
      (popR (interpR rootProgram) (.success Val.unit) stack fiber.frame).1 := by
  have walk := popR_hostTyped (rootProgram : ProgramSource) (interpR rootProgram) world
    (machineOf fiber) Api.root (hookLaws_interpR _ world) host (.success Val.unit) fiber.frame
    unit_ok (provenance _ rfl rfl)
  rw [walk_eq] at walk ⊢
  exact marker_outcome rfl walk

end Double

namespace AnswerThenArrow

def stack : List ScopeFrame := [.answer iaNext, .resume .onSuccess yieldNext]
def fiber : RFiber := fiberOf yieldCurrent stack 1

theorem host : HostStack (rootProgram : ProgramSource) world (machineOf fiber) Api.root
    (EffTy.pure .unit) natTy stack :=
  .cons (.inl (iaSlot world)) (arrow rfl rfl (.nil natTy))

/-- The answer slot completes with the same success, which the arrow turns into its marker. -/
theorem walk_eq : popR (interpR rootProgram) (.success Val.unit) stack fiber.frame =
    ({ fiber.frame with current := marker, stack := [] }, none) := rfl

theorem reaches_marker :
    HostMarker (rootProgram : ProgramSource) world (machineOf fiber) Api.root natTy
      (popR (interpR rootProgram) (.success Val.unit) stack fiber.frame).1 := by
  have walk := popR_hostTyped (rootProgram : ProgramSource) (interpR rootProgram) world
    (machineOf fiber) Api.root (hookLaws_interpR _ world) host (.success Val.unit) fiber.frame
    unit_ok (provenance _ rfl rfl)
  rw [walk_eq] at walk ⊢
  exact marker_outcome rfl walk

end AnswerThenArrow

end Test.Program.HostWalkControls

#print axioms Test.Program.HostWalkControls.Double.reaches_marker
#print axioms Test.Program.HostWalkControls.AnswerThenArrow.reaches_marker
