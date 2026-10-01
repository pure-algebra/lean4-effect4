import Effect4.Laws.Program.Guard.Single
import Test.Api.HostSessionContract

/-!
Seat F probe (2026-10-01, landing item 3, M2): why `Guard/Single.lean`'s fold inductions cannot be
replaced by an instance of the tree's `DecisionLift` (`Laws/Machine/Lift.lean:302`).

`DecisionLift` bundles thirteen premises; the fold lifts (`fireFold_lift`, `fireState_lift`,
`flushAllState_lift`, `advanceState_lift`) read eight of them, but an instance must supply all
thirteen, and `interrupt` must keep the invariant across the edit an `interruptFrom` decision makes
for *any* target. `Held` (every fiber parked at the guard token) is not kept by that edit:
`interruptRecord` unparks an idle, interruptible fiber (`Machine/Fibers.lean:817-823`). The guard's
own decision lemma excludes interrupts with a premise (`held_steppedBy`'s `NoCancel`), which the
lift's field cannot carry.

Proved here at a concrete machine: the checked host session's parked machine
(`Test/Api/HostSessionContract.lean`, `parked`: one root fiber parked at token 0 on `external 0`).
`Held` holds there (`held_parked`), and after the interrupt edit of the root fiber `Held` fails
(`edit_unparks`), so the `interrupt` field, specialised to `J := Held`, is false
(`interrupt_field_false`). Red control: `held_parked` itself — the refutation is not vacuous.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SeatF.HeldInterrupt

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.SingleGuard

abbrev p : NativeEff := Test.Api.HostSessionContract.program
abbrev table : RowTable := Test.Api.HostSessionContract.table
abbrev m0 : NativeMachine := Test.Api.HostSessionContract.parked.machine
abbrev req : NativeOp × Val := (.external 0, .nat 2)

theorem root_isSome : (m0.fiber? Api.root).isSome = true := by decide +kernel

/-- The root fiber of the parked machine. -/
def t0 : NFiber := (m0.fiber? Api.root).get root_isSome

theorem root_lookup : m0.fiber? Api.root = some t0 := (Option.some_get root_isSome).symm

/-- Red control: `Held` holds at the parked machine, so the refutation below is not vacuous. -/
theorem held_parked : Held m0 Api.root 0 req := by
  refine ⟨?_, ?_, ?_⟩
  · show ∀ f ∈ m0.fibers, f.id = Api.root ∧ f.parked = .withGuard 0
    decide +kernel
  · decide +kernel
  · decide +kernel

/-- The interrupt edit of the root fiber unparks it, so `Held`'s first clause fails. -/
theorem edit_unparks :
    letI := evaluatorFor p table
    ¬ ∀ f ∈ (Lift.interruptEdit (interpOf p table) m0 none ReasonAnnotations.empty Api.root t0).fibers,
        f.id = Api.root ∧ f.parked = .withGuard 0 := by
  decide +kernel

/-- **The obstacle.** `DecisionLift`'s `interrupt` premise at `J := Held` is false. -/
theorem interrupt_field_false :
    letI := evaluatorFor p table
    ¬ ∀ (m : NativeMachine) (who : Option FiberId) (extra : ReasonAnnotations Ann)
        (target : FiberId) (t : NFiber),
        Held m Api.root 0 req → m.fiber? target = some t →
        Held (Lift.interruptEdit (interpOf p table) m who extra target t) Api.root 0 req := by
  intro field
  exact edit_unparks (field m0 none ReasonAnnotations.empty Api.root t0 held_parked root_lookup).only

end SeatF.HeldInterrupt

#print axioms SeatF.HeldInterrupt.held_parked
#print axioms SeatF.HeldInterrupt.edit_unparks
#print axioms SeatF.HeldInterrupt.interrupt_field_false
