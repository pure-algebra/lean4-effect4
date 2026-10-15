import Test.Dogfood.Proofs.HostTimeoutNumberMessages

/-!
Concepts: scope-lifetime-finalization R11 and reactive-scheduling R9.
Question: the active attempt's reference writes retain every passive numeric role.
Consumer: the joint count and cleanup native producer of both Timeout goals.
Reach: structural root control, timer siblings, and already retired fibers, uniformly over completed views.
Limit: the actual protocol must establish its unique active attempt and retirement conditions.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberPassive
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutFlow HostTimeoutState HostTimeoutNumberConfiguration

/-- Only the active attempt owns heap-dependent pending numeric code. -/
inductive Passive : Role → Prop
  | root (suffix : List NCode) : Passive (.rootRead suffix)
  | timer : Passive .timer
  | retired : Passive .retired

/-- Every passive frame retains its actual control at an arbitrary sibling reference write. -/
theorem frame_store (before after : Effect4.Program.NativeMachine) (role : Role)
    (frame : HostTimeoutFrames.NativeFrame) (passive : Passive role) (held : FrameAt before role frame) :
    FrameAt after role frame := by
  cases passive with
  | root suffix => exact held
  | timer =>
      intro view
      exact HostTimeoutNumberTimer.frame_store view before.state after.state frame (held view)
  | retired => trivial

/-- Passive published exits contain no assertion about the active attempt's reference image. -/
theorem exit_store (machine : Effect4.Program.NativeMachine) (role : Role) (exit : ExitV)
    (passive : Passive role) : ExitAt machine role exit := by
  cases passive <;> trivial

/-- A sibling reference write retains every execution and interruption permission of a passive fiber. -/
theorem fiber_store (before after : Effect4.Program.NativeMachine) (role : Role)
    (fiber : Effect4.Program.SourceScope.SourceFiber) (passive : Passive role) (held : FiberAt before role fiber) :
    FiberAt after role fiber := by
  constructor
  · exact frame_store before after role fiber.frame passive held.frame
  · intro selected found
    exact exit_store after role selected passive
  · exact held.retired
  · exact held.recorded
  · intro cause clean live idle interruptible
    exact frame_store before after role _ passive (held.immediate cause clean live idle interruptible)
  · intro context same heap installed
    cases passive <;> cases same

/-- The role census names the one heap-dependent attempt without duplicating machine state. -/
def OnlyAttempt (world : HostTimeoutNumberConfiguration.World) (active : FiberId) (context : CountContext) : Prop :=
  ∀ id role, (id, role) ∈ world.roles → (id = active ∧ role = .pending context) ∨ Passive role

/-- Every other actual stored fiber receives a passive role from the same census. -/
theorem other_passive (world : HostTimeoutNumberConfiguration.World) (active : FiberId) (context : CountContext)
    (id : FiberId) (role : Role) (census : OnlyAttempt world active context)
    (assigned : (id, role) ∈ world.roles) (other : id ≠ active) : Passive role := by
  rcases census id role assigned with ⟨same, pending⟩ | passive
  · exact False.elim (other same)
  · exact passive

end Test.Dogfood.Proofs.HostTimeoutNumberPassive
