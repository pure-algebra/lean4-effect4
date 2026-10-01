import Effect4
import Effect4.Laws

/-!
Seat ORGANIZATION probe (2026-10-01): is `Guard/Single.lean`'s hand induction `held_driveState`
(lines 196-215: induction on fuel, cases on the command list) a second route to the generic loop
lift `Machine.Lift.driveState_lift_unit` (row 110)? Proved here by restating it as one
application of the lift to the existing per-command lemma `held_driveStep`, with the statement
copied verbatim, and by checking the copy has the tree theorem's exact type.
Red control: the lift's step premise is required; dropping it (the `fail_if_success` block)
must not elaborate.
-/

set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.SingleGuard

theorem held_driveState_viaLift (p : NativeEff) (table : RowTable) (fuel : Nat)
    {m : NativeMachine} {fiber : FiberId} {token : Nat} {request : NativeOp × Val}
    (h : Held m fiber token request) (commands : List NCmd) (quiet : QuietQueue fiber token commands) :
    letI := evaluatorFor p table
    Held (driveState (interpOf p table) fuel m commands).1 fiber token request ∧
      QuietQueue fiber token (driveState (interpOf p table) fuel m commands).2 := by
  letI := evaluatorFor p table
  exact Effect4.Machine.Lift.driveState_lift_unit (interpOf p table)
    (fun m cmds => Held m fiber token request ∧ QuietQueue fiber token cmds)
    (fun _ c rest _ hi => held_driveStep p table hi.1 c rest (hi.2 c (List.mem_cons_self ..))
      (fun c' hc => hi.2 c' (List.mem_cons_of_mem _ hc)))
    fuel m commands ⟨h, quiet⟩

/-- The copy states exactly what the tree's hand-induction theorem states. -/
example : @held_driveState_viaLift = @held_driveState := rfl

#print axioms held_driveState_viaLift

/-- Red control: without the per-command premise the lift cannot be applied. -/
example : True := by
  fail_if_success
    (have := fun (p : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : FiberId)
        (token : Nat) (request : NativeOp × Val) (cmds : List NCmd) =>
      (letI := evaluatorFor p table
       Effect4.Machine.Lift.driveState_lift_unit (interpOf p table)
        (fun m cmds => Held m fiber token request ∧ QuietQueue fiber token cmds)
        (fun _ _ _ _ hi => hi) 0 m cmds))
  trivial
