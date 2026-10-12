import OperationCounterCommandProbe
import Effect4.Laws.Program.PlaceFunding.Commands

/-!
Concept: reactive-scheduling R11.
Question: actual operation accounting serves the two original Timeout numeric history claims.
Consumer: the count-entry prefix needs the installed owner counter after actual commands.
Reach: one command, the native evaluator, and distinct stored fiber ids.
This instance supplies no public command room, source progress, or completed cleanup history.
-/
set_option autoImplicit false
namespace Effect4.Program.OperationCount
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- An actual command adds at most the selected owner's loop allowance to its stored counter. -/
theorem command_count (owner : FiberId) (root : NativeEff) (table : RowTable)
    (machine : NativeMachine) (command : Native.NCmd) (rest : List Native.NCmd)
    (ok : Effect4.Machine.ForkLedger.Invariant.Ok machine) :
    letI := evaluatorFor root table
    countAt owner (driveStep (interpOf root table) machine command rest).1 ≤
      countAt owner machine + PlaceFunding.commandAllowance
        (fun _ id _ => if id = owner then 1 else 0) machine command := by
  letI := evaluatorFor root table
  have funded := (funded_iff owner (countAt owner machine) machine [] [] ok.idsUnique).mpr
    (Nat.le_refl _)
  have after := PlaceFunding.command_funded root table (control owner) (no_queue owner) (events owner)
    (stores owner (interpOf root table)) (administration owner (interpOf root table))
    (fun _ => True) (fun _ id _ => if id = owner then 1 else 0) (evaluation owner root table)
    machine command rest ok True.intro (inputs machine command) funded
  exact (funded_iff owner _ _ [] []
    (Native.driveStep_ok root table machine command rest ok).idsUnique).mp after

end Effect4.Program.OperationCount
