import Test.Api.TypedReplies
import Effect4.Laws.Api.HostDrive

/-! Finite controls for the mandatory guard recommendation.
These controls read the existing call-instance admission and driver. They add no theorem.
Consumer: the host-session-protocol plan's deployment boundary, R6 and R13.
They establish neither physical host effects nor a denotation outside the named fragments. -/

set_option autoImplicit false
namespace Refinement.Guard
open Effect4 Effect4.Program Effect4.Machine
open Test.Api.TypedReplies

def checked : Option Api.Built :=
  (Api.Built.ofProgram table program).toOption

def validHost : Run.Reactor Nat :=
  fun _ _ st => some (some1.completion, st + 1)

def badHost : Run.Reactor Nat :=
  fun _ _ st => some (.ofExit (.success (.str "invalid")), st + 1)

def absentHost : Run.Reactor Nat := fun _ _ _ => none

-- An accepted instantiated reply fails the raw-row guard.
#guard bound.map (fun s => (Api.HostSession.submit s some1).phase) = some .preflight
#guard Run.answerAdmits [] first some1.completion = false
#guard validHost first (.list [.nat 1]) 0 = some (some1.completion, 1)
#guard (validHost.guardRows []) first (.list [.nat 1]) 0 = none

-- Filtering a valid answer removes its exit and next host state.
#guard checked.map (fun b =>
  let u := Run.runWith b validHost 0 "review" {} 16
  let g := Run.runWith b (validHost.guardRows b.app.types) 0 "review" {} 16
  (u.1.exit, u.2, g.1.exit, g.2)) ==
  some (some (.success (.some (.nat 1))), 1, none, 0)

-- Invalid and absent replies produce identical observations, journals, phases and state.
#guard checked.map (fun b =>
  let g := Run.runWith b (badHost.guardRows b.app.types) 0 "review" {} 16
  let n := Run.runWith b absentHost 0 "review" {} 16
  decide (g.1.observe = n.1.observe) &&
  decide (g.1.journal = n.1.journal) &&
  decide (g.1.phases = n.1.phases) &&
  decide (g.2 = n.2)) = some true

-- The existing unguarded driver retains the refused attempt and the resulting host state.
#guard checked.map (fun b =>
  let u := Run.runWith b badHost 0 "review" {} 16
  (u.2, u.1.phases.any fun p => decide (p = .refused .envelope))) =
  some (1, true)

end Refinement.Guard
