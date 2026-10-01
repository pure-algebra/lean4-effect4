import Effect4.Laws.Program.Guard.Single
import Test.Api.HostSessionContract

/-!
# Why the guard's fold facts go through `FoldLift` (decisions row 150)

`Machine.Lift.DecisionLift` bundles thirteen premises; the fold lifts (`fireFold_lift`,
`fireState_lift`, `flushAllState_lift`, `advanceState_lift`) read eight of them, packaged as
`Machine.Lift.FoldLift`. The other five include `interrupt`: the invariant must survive the edit an
`interruptFrom` decision makes for any target (`Machine.Lift.interruptEdit`). The guard's `Held`
(every fiber parked at the guard token) does not survive it, because `interruptRecord` unparks an
idle, interruptible fiber (`Machine/Fibers.lean`). The guard's own decision lemma excludes
interrupts by a premise (`held_steppedBy`'s `NoCancel`) that the lift's field cannot carry.

Proved here at a concrete machine, the checked host session's parked machine
(`Test/Api/HostSessionContract.lean`, `parked`: one root fiber parked at token 0 on `external 0`):
`Held` holds there (`held_parked`, the red control: the refutation is not vacuous); after the
interrupt edit of the root fiber it fails (`edit_unparks`); so the `interrupt` field at `J := Held`
is false (`interrupt_field_false`) and no decision lift carries `Held`, whatever its queue,
snapshot and admission facts (`no_decisionLift`). The same `Held` is a fold lift
(`held_is_foldLift`), which is how `held_fireFold`, `held_fireState`, `held_flushAllState` and
`held_advanceState` (`Laws/Program/Guard/Single.lean`) are proved. First proved off-tree by seat F
(`docs/research/2026-10-01-landing/seat-F/probes/HeldInterruptRefuted.lean`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Program.GuardFoldLift

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

/-- `DecisionLift`'s `interrupt` premise at `J := Held` is false. -/
theorem interrupt_field_false :
    letI := evaluatorFor p table
    ¬ ∀ (m : NativeMachine) (who : Option FiberId) (extra : ReasonAnnotations Ann)
        (target : FiberId) (t : NFiber),
        Held m Api.root 0 req → m.fiber? target = some t →
        Held (Lift.interruptEdit (interpOf p table) m who extra target t) Api.root 0 req := by
  intro field
  exact edit_unparks (field m0 none ReasonAnnotations.empty Api.root t0 held_parked root_lookup).only

/-- **The obstacle.** No decision lift carries `Held`, whatever its queue, snapshot and admission
facts. -/
theorem no_decisionLift
    (I : Unit → NativeMachine → List NCmd → Prop) (O : Unit → NativeMachine → List NTask → Prop)
    (A : Unit → NativeMachine → NativeDecision → Prop) :
    letI := evaluatorFor p table
    ¬ Lift.DecisionLift Lift.unitOrder (interpOf p table) (fun _ m => Held m Api.root 0 req) I O A := by
  letI := evaluatorFor p table
  intro lift
  exact interrupt_field_false (lift.interrupt ())

/-- **The repair.** The same `Held` is a fold lift. -/
theorem held_is_foldLift :
    letI := evaluatorFor p table
    Lift.FoldLift Lift.unitOrder (interpOf p table) (fun _ m => Held m Api.root 0 req)
      (fun _ _ cmds => QuietQueue Api.root 0 cmds)
      (fun _ _ ts => ∀ t ∈ ts, (Api.root, 0) ∉ taskKeys t) :=
  held_foldLift p table Api.root 0 req

/-- info: 'Test.Program.GuardFoldLift.held_parked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms held_parked
/-- info: 'Test.Program.GuardFoldLift.edit_unparks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms edit_unparks
/-- info: 'Test.Program.GuardFoldLift.interrupt_field_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms interrupt_field_false
/-- info: 'Test.Program.GuardFoldLift.no_decisionLift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_decisionLift
/-- info: 'Test.Program.GuardFoldLift.held_is_foldLift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms held_is_foldLift

end Test.Program.GuardFoldLift
