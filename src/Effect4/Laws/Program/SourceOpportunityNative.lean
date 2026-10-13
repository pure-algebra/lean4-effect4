import Effect4.Laws.Program.SourceOpportunityMachine
import Effect4.Laws.Machine.Handshake
import Effect4.Laws.Machine.WriterWeights

/-!
Concept: scope-lifetime-finalization R11.
Consumer: actual native evaluator closure for application source-use bounds.
The debit excludes the acting stored row until the returned fiber is installed.
It measures the existing machine, frame and trace fields only. The action and countdown arms are
the ledger-generic `PlaceFunding.action_debit` and `PlaceFunding.countdown_debit`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- The actual evaluator spends only its acting frame's source reservation.
Consumer: command settlement and the source-use history invariant. -/
def Debit (root : NativeEff) (q : List Nat) (m : NativeMachine) (fiber : SourceFiber)
    (next : SourceIteration) : Prop :=
  recorded q next.machine + outside root q fiber.id next.machine + frame root q next.fiber.frame ≤
    recorded q m + outside root q fiber.id m + frame root q fiber.frame

/-- Closing a source-owned scope installs only code with no selected source opportunity.
Consumer: the close arm of `native_action_debit`. -/
theorem close_scope_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (completed : List (FiberId × ExitV)) (scope : Nat) (exit : ExitV) (flag : Bool)
    (closer : FiberId) (clear : ClearFinalizers root q) (state next : Stores)
    (owned : ScopesAt root state.scopes) (program : NCode)
    (closed : (interpAt root completed table).closeScope scope exit flag closer state =
      some (next, some program)) :
    current root q program = 0 := by
  change (storesCloseScope scope exit flag state).map (fun result => (result.1, result.2.map embed)) =
    some (next, some program) at closed
  cases step : storesCloseScope scope exit flag state with
  | none => rw [step] at closed; cases closed
  | some result =>
    obtain ⟨after, code⟩ := result
    rw [step] at closed
    cases code with
    | none => cases closed
    | some code =>
      cases closed
      unfold storesCloseScope at step
      cases snapshot : scopeCloseSnapshot scope exit state with
      | none => rw [snapshot] at step; cases step
      | some result =>
        obtain ⟨closedState, strategy, order⟩ := result
        have slots := close_snapshot_at root scope exit state closedState strategy order owned snapshot
        simp only [snapshot, Option.pure_def] at step
        cases order with
        | nil => cases step
        | cons first rest =>
          cases rest with
          | nil =>
            cases step
            have finZero := fin_program_zero root q clear first exit (slots.2.1 first (.head _))
            simpa only [embed, current, cata_prim, name, push, Nat.add_zero] using finZero
          | cons second tail =>
            cases step
            rfl

end Effect4.Program.SourceScope.Opportunities
