import Effect4.Laws.Program.FinalizerNativeIteration
import Effect4.Laws.Program.PlaceFunding.QueueProjection

/-!
Concept: scope-lifetime-finalization, R11.
Question: actual command accounting serves once_placed_outside_census.
Consumer: full finalizer source funding along raw histories.
Full source annotations license evaluation; native terminal replies license imported code.
Race launch spends the actual unlaunched program reservation.
The local command theorem establishes neither those history invariants nor release custody.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- The full annotation needed by an actual native evaluation. -/
def EvaluationReady (q : List Nat) (machine : NativeMachine) : Prop :=
  (∀ fiber ∈ machine.fibers, TemplateFrame q fiber.frame) ∧
    ScopesAt q machine.state.scopes ∧ (machine.races.map Race.id).Nodup

/-- Imported replies have a separate zero-weight permission in the common command producer. -/
abbrev commandLedger (root : NativeEff) (q : List Nat) : PlaceFunding.Ledger :=
  PlaceFunding.withoutPending (ledger root q)

/-- Full native evaluation supplies the common zero-charge command obligation. -/
theorem command_evaluation (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    PlaceFunding.Evaluation (commandLedger root q) (EvaluationReady q) root table (fun _ _ _ => 0) := by
  apply PlaceFunding.Evaluation.from_debits (PlaceFunding.withoutPending_noPending _) root table
    (EvaluationReady q)
  · intro machine fiber yielding _ ready found
    have frame := ready.1 fiber (RunMachine.mem_of_fiber? found)
    exact PlaceFunding.withoutPending_debit _ _ _ _
      (native_debit root q table placed machine fiber yielding (template_frame_at q _ frame)
        frame.1 ready.2.1 ready.2.2)
  · intro machine fiber yielding _ ready found
    exact PlaceFunding.withoutPending_debit _ _ _ _
      (iteration_debit root q table placed machine fiber yielding
        (ready.1 fiber (RunMachine.mem_of_fiber? found)) ready.2.1 ready.2.2)

/-- Metadata keeps the reservation held by a race's actual unlaunched programs. -/
theorem command_race_weights (root : NativeEff) (q : List Nat) :
    PlaceFunding.RaceWeights (commandLedger root q) where
  metadata := by
    intro old next same
    change (next.programs.map (current root q)).sum = (old.programs.map (current root q)).sum
    rw [same]

/-- One actual command retains source funding, with no lexical or race-free restriction. -/
theorem command_funded (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (cap : Nat)
    (machine : NativeMachine) (command : SourceScope.SourceCommand) (rest : List SourceScope.SourceCommand)
    (valid : ForkLedger.Invariant.Ok machine) (ready : EvaluationReady q machine)
    (reply : ∀ owner token code, command = .resume owner token code → SourceScope.TerminalReply code)
    (funded : (ledger root q).Funded cap machine [] []) :
    letI := evaluatorFor root table
    (ledger root q).Funded cap
      (driveStep (interpOf root table) machine command rest).1 [] [] := by
  letI := evaluatorFor root table
  have control' : PlaceFunding.Control (commandLedger root q) (Free root q) := (control root q).withoutPending
  have events' : PlaceFunding.Events (commandLedger root q) := (events root q).withoutPending
  have stores' : PlaceFunding.StoreHooks (commandLedger root q) (interpOf root table) := (stores root q table).withoutPending
  have admin' : PlaceFunding.Administration (commandLedger root q) (Free root q) (interpOf root table) :=
    (administration root q table).withoutPending
  have result := PlaceFunding.command_funded_at root table control'
    (PlaceFunding.withoutPending_noPending _) events' stores' admin'
    (EvaluationReady q) (fun _ _ _ => 0) (command_evaluation root q table placed)
    machine command rest valid ready
    (fun owner token code selected => terminal_zero root q code (reply owner token code selected))
    (fun m => (m.races.map Race.id).Nodup)
    (fun _ _ same held => by rw [same]; exact held)
    (fun m key old next found same programs distinct =>
      ⟨rfl, fun ok => ⟨ForkLedger.Invariant.updateRace_ok ok next,
        PlaceFunding.race_balance (command_race_weights root q) m old next distinct
          (by simpa only [RunMachine.id_of_race? found] using found) same programs⟩⟩)
    ready.2.2
    (fun raceId _ => by
      have same := (Machine.Lift.driveStep_append (interpOf root table) machine
        (.launch raceId) [] rest).1
      simp only [List.nil_append] at same
      rw [same]
      exact PlaceFunding.withoutPending_balance (ledger root q) machine _ [.launch raceId] _ rfl
        (launch_balance root table q machine raceId [] [] ready.2.2))
    ((PlaceFunding.withoutPending_funded_iff _ _ _).mpr funded)
  rw [PlaceFunding.commandAllowance_zero, Nat.add_zero] at result
  exact (PlaceFunding.withoutPending_funded_iff _ _ _).mp result

end Effect4.Program.FinalizerSource
