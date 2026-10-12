import Effect4.Laws.Program.SourceOpportunityCommands
import Effect4.Laws.Program.PlaceFunding.History
import Effect4.Laws.Program.PlaceLedgerConnect
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.ReleaseTrace

/-!
Concept: scope-lifetime-finalization R11.
Consumer: original Workers registration and Atomic cleanup bounds.
The existing decision lift carries the existing source configuration and its numeric budget.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program Effect4.Run

/-- Actual admitted decision transport retains the original configuration and source budget.
Consumer: the universal application source-use history bound. -/
theorem budget_decision_lift (root : NativeEff) (q : List Nat) (cap : Nat)
    (fragment : Fragment root) (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q)
    (table : RowTable) (sequential : SequentialSource root) (raceFree : RaceFreeSource root) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ m => ConfigurationAt root m ∧ ForkLedger.Invariant.Ok m ∧ recorded q m + fibers root q m ≤ cap)
      (fun _ _ commands => CommandsAt root commands) (fun _ _ tasks => TasksAt root tasks) (fun _ _ _ => True) := by
  letI := evaluatorFor root table
  have edits : Lift.MachineEdits (interpOf root table)
      (fun m => ForkLedger.Invariant.Ok m ∧ recorded q m + fibers root q m ≤ cap) := by
    have predicate : PlaceFunding.Holds (PlaceLedgerConnect.source root q) cap =
        (fun m => ForkLedger.Invariant.Ok m ∧ recorded q m + fibers root q m ≤ cap) := by
      funext m
      exact propext (and_congr_right fun _ => PlaceLedgerConnect.source_funded root q cap m)
    rw [← predicate]
    exact PlaceFunding.edits (source_control root q) (source_no_queue root q) (source_events root q)
        cap (interpOf root table) (fun _ _ => Nat.le_refl _) (fun _ _ _ _ => Nat.le_refl _)
  apply (reply_decision_lift root fragment table).withMachineFact _ ?_ edits ?_
  · intro tasks world m command rest running source held
    have queue := (source.2 running).1
    have ledger := ForkLedger.Invariant.Native.driveStep_ok root table m command rest held.1
    have bound := command_debit root q fragment clearFin clearLoop table m command rest
      sequential raceFree source.1 held.1 (queue command (.head _))
    exact ⟨ledger, Nat.le_trans bound held.2⟩
  · intro world m id token answer owned held running admitted
    have prepared := prepare_reply_at root table m id token answer
    have ledger := ForkLedger.Invariant.Native.driveStep_ok root table
      {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1}
      (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2) [.drainDue] held.1
    have bound := resume_command_debit root q table
      {m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1}
      id token (prepareAsyncAnswer (interpOf root table) m id token answer).2 [.drainDue] held.1.idsUnique prepared.2.2
    exact ⟨ledger, Nat.le_trans bound held.2⟩

/-- Every actual decision retains the combined recorded and live source budget.
Consumer: the original admitted-history bound for application source sites. -/
theorem decision_budget (root : NativeEff) (q : List Nat) (cap : Nat)
    (fragment : Fragment root) (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q)
    (table : RowTable) (sequential : SequentialSource root) (raceFree : RaceFreeSource root)
    (fuel : Nat) (m : NativeMachine) (decision : NativeDecision)
    (owned : ConfigurationAt root m) (ledger : ForkLedger.Invariant.Ok m)
    (bounded : recorded q m + fibers root q m ≤ cap) :
    ConfigurationAt root (steppedBy root fuel table m decision) ∧
      ForkLedger.Invariant.Ok (steppedBy root fuel table m decision) ∧
      recorded q (steppedBy root fuel table m decision) +
        fibers root q (steppedBy root fuel table m decision) ≤ cap := by
  letI := evaluatorFor root table
  obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift
    (budget_decision_lift root q cap fragment clearFin clearLoop table sequential raceFree)
    fuel () m decision ⟨owned, ledger, bounded⟩ trivial
  exact moved

/-- The original admitted-history carrier retains at most one selected source opportunity.
The source restrictions are discharged by the actual Atomic and Workers programs.
This invariant establishes neither progress nor arbitrary-source control linearity. -/
theorem history_budget (b : Api.Built) (q : List Nat) (fragment : Fragment b.program)
    (clearFin : ClearFinalizers b.program q) (clearLoop : ClearLoops b.program q)
    (sequential : SequentialSource b.program) (raceFree : RaceFreeSource b.program)
    (compileFuel : Nat) (m : NativeMachine) (history : HistoryOf b compileFuel m) :
    recorded q m + fibers b.program q m ≤ 1 := by
  have kept := history_keeps b compileFuel
    (fun m => ConfigurationAt b.program m ∧ ForkLedger.Invariant.Ok m ∧
      recorded q m + fibers b.program q m ≤ 1)
    ⟨load_at b.program fragment compileFuel, ForkLedger.Invariant.load_ok b.program compileFuel,
      load_budget b.program q compileFuel⟩
    (fun before row held _ => decision_budget b.program q 1 fragment clearFin clearLoop b.table
      sequential raceFree row.1 before row.2 held.1 held.2.1 held.2.2) m history
  exact kept.2.2

/-- Every actual acquisition registration event consumes the selected source reservation.
Consumer: the original Workers registration count. -/
theorem registered_event_le (q : List Nat) (ev : ReleaseTrace.Event) :
    (if ReleaseTrace.registeredAt q ev then 1 else 0) ≤ runEvent q ev := by
  letI : LawfulBEq (List Nat) := @List.instLawfulBEq Nat _ Nat.instLawfulBEq
  letI : ReflBEq (List Nat) := @List.instReflBEq Nat _ Nat.instLawfulBEq.toReflBEq
  fun_cases ReleaseTrace.registeredAt q ev with
  | case1 id body a capture =>
    change (if capture.path == q then 1 else 0) ≤ here q capture.path
    by_cases same : capture.path = q
    · simp only [same, beq_self_eq_true, ↓reduceIte, here]
      exact Nat.le_refl 1
    · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ↓reduceIte, here, same]
      exact Nat.le_refl 0
  | case2 ev negative => exact Nat.zero_le _

/-- The actual trace registration count is bounded by consumed source reservations.
This reads the existing trace and introduces no execution carrier. -/
theorem registrations_le_recorded (q : List Nat) (m : NativeMachine) :
    m.trace.countP (ReleaseTrace.registeredAt q) ≤ recorded q m := by
  unfold recorded
  induction m.trace with
  | nil => exact Nat.le_refl 0
  | cons ev tail ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons]
    have one := registered_event_le q ev
    omega

/-- An actual selected onExit push consumes its source reservation.
Consumer: Atomic cleanup registration uniqueness at each request source. -/
theorem exit_registered_event_le (q : List Nat) (ev : ReleaseTrace.Event) :
    (if (match ev with
      | .frame _ (.pushed (.onExit _ (.fin p) _)) => p.path == q
      | _ => false) then 1 else 0) ≤ runEvent q ev := by
  letI : LawfulBEq (List Nat) := @List.instLawfulBEq Nat _ Nat.instLawfulBEq
  letI : ReflBEq (List Nat) := @List.instReflBEq Nat _ Nat.instLawfulBEq.toReflBEq
  split
  · rename_i id body p flag
    change (if p.path == q then 1 else 0) ≤ here q p.path
    by_cases same : p.path = q
    · simp only [same, beq_self_eq_true, ↓reduceIte, here]
      exact Nat.le_refl 1
    · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ↓reduceIte, here, same]
      exact Nat.le_refl 0
  · exact Nat.zero_le _

/-- The actual trace's selected onExit pushes fit within recorded source reservations.
Consumer: Atomic cleanup source uniqueness, independent of finalizer custody. -/
theorem exit_registrations_le_recorded (q : List Nat) (m : NativeMachine) :
    m.trace.countP (fun ev => match ev with
      | .frame _ (.pushed (.onExit _ (.fin p) _)) => p.path == q
      | _ => false) ≤ recorded q m := by
  unfold recorded
  induction m.trace with
  | nil => exact Nat.le_refl 0
  | cons ev tail ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons]
    have one := exit_registered_event_le q ev
    have combined := Nat.add_le_add ih one
    rw [Nat.add_comm ((tail.map (runEvent q)).sum) (runEvent q ev)] at combined
    exact combined

end Effect4.Program.SourceScope.Opportunities
