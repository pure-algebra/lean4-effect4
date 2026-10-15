import Effect4.Laws.Program.FinalizerConfiguration
import Effect4.Laws.Program.Guard.Lift
import Effect4.Laws.Program.PlaceFunding.History
import Effect4.Laws.Machine.LiftCoupledFact

/-!
Concept: scope-lifetime-finalization R11.
Question: the full source ledger serves FinalizerRun.once_placed_outside_census.
Consumer: the final registration bound after release custody supplies its transferred credits.
The common driver retains actual source locations, distinct race rows and source funding together.
The ledger counts release-start credits as production; it does not establish their custody.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Full source ownership accompanies the existing guard and its command authority. -/
theorem guarded_configuration_lift (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    letI := evaluatorFor root table
    Lift.DecisionLift (Lift.pairOrder Lift.unitOrder Lift.unitOrder) (interpOf root table)
      (fun _ machine => Guard.GuardState machine ∧
        CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine)
      (fun _ machine commands => Guard.DriverQueue root table machine commands ∧
        CodeClosure.Configuration.CommandsAt (configurationModel q) commands)
      (fun _ machine tasks => Guard.DriverTasks machine tasks ∧
        CodeClosure.Configuration.TasksAt (configurationModel q) tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  exact (Guard.state_decision_lift root table).withCoupledFact
    ((configuration_lift root q table placed).asCoupled (by intros; trivial))

/-- The existing place ledger advances alongside actual configuration and driver permissions. -/
theorem funded_configuration_lift (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (cap : Nat) :
    letI := evaluatorFor root table
    Lift.DecisionLift (Lift.pairOrder Lift.unitOrder Lift.unitOrder) (interpOf root table)
      (fun _ machine => (Guard.GuardState machine ∧
        CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine) ∧
        PlaceFunding.Holds (commandLedger root q) cap machine)
      (fun _ machine commands => Guard.DriverQueue root table machine commands ∧
        CodeClosure.Configuration.CommandsAt (configurationModel q) commands)
      (fun _ machine tasks => Guard.DriverTasks machine tasks ∧
        CodeClosure.Configuration.TasksAt (configurationModel q) tasks)
      (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  have edits := PlaceFunding.edits_at (control root q).withoutPending (events root q).withoutPending
    cap (interpOf root table) (fun _ _ => Nat.le_refl 0) (fun _ _ _ _ => Nat.le_refl 0)
  apply (guarded_configuration_lift root q table placed).withMachineFact
    (PlaceFunding.Holds (commandLedger root q) cap) ?_ edits ?_
  · intro tasks world machine command rest running held funded
    have ready : EvaluationReady q machine :=
      ⟨fun fiber member => (held.1.2.fibers fiber member).frame, held.1.2.scopes, held.1.1.raceIds⟩
    have replies : ∀ owner token code, command = .resume owner token code → SourceScope.TerminalReply code := by
      intro owner token code selected
      have allowed := ((held.2 running).1.2) command (.head _)
      rw [selected] at allowed
      exact allowed.2
    exact ⟨ForkLedger.Invariant.Native.driveStep_ok root table machine command rest funded.1,
      command_funded root q table placed cap machine command rest funded.1 ready replies funded.2⟩
  · intro world machine id token answer held funded running allowed
    have prepared := SourceScope.prepare_reply_at root table machine id token answer
    have after := edits.prepare machine id token answer funded
    have source : CodeClosure.Configuration.ConfigurationAt (configurationModel q)
        {machine with state := (prepareAsyncAnswer (interpOf root table) machine id token answer).1} := by
      refine ⟨held.2.fibers, held.2.races, ?_⟩
      rw [prepared.1]
      exact held.2.scopes
    have ready : EvaluationReady q
        {machine with state := (prepareAsyncAnswer (interpOf root table) machine id token answer).1} :=
      ⟨fun fiber member => (source.fibers fiber member).frame, source.scopes, held.1.raceIds⟩
    refine ⟨ForkLedger.Invariant.Native.driveStep_ok root table _ _ [.drainDue] after.1, ?_⟩
    apply command_funded root q table placed cap _ _ [.drainDue] after.1 ready ?_ after.2
    intro owner fresh code same
    cases same
    exact prepared.2.2

/-- Every raw native history retains the full source balance at every command budget. -/
theorem source_funded_reachable (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (compileFuel : Nat) (machine : NativeMachine)
    (reached : Guard.Reachable root table compileFuel machine) :
    (ledger root q).Funded 1 machine [] [] := by
  have initial : (Guard.GuardState (Api.load root compileFuel) ∧
      CodeClosure.Configuration.ConfigurationAt (configurationModel q) (Api.load root compileFuel)) ∧
      PlaceFunding.Holds (commandLedger root q) 1 (Api.load root compileFuel) :=
    ⟨⟨Guard.guardState_load root compileFuel, configuration_load root q compileFuel⟩,
      ForkLedger.Invariant.load_ok root compileFuel, load_funded root q compileFuel⟩
  have preserved := Guard.reachable_lift_pure root table compileFuel
    (fun machine => (Guard.GuardState machine ∧
      CodeClosure.Configuration.ConfigurationAt (configurationModel q) machine) ∧
      PlaceFunding.Holds (commandLedger root q) 1 machine) initial
    (fun before fuel decision held => by
      letI := evaluatorFor root table
      obtain ⟨_, _, kept⟩ := Lift.stepDecisionState_lift (funded_configuration_lift root q table placed 1)
        fuel ((), ()) before decision held trivial
      exact kept) machine reached
  exact preserved.2.2

end Effect4.Program.FinalizerSource
