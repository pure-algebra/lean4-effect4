import Effect4.Laws.Program.SourceOpportunityCommands
import Effect4.Laws.Program.PlaceFunding.Run
import Effect4.Laws.Program.PlaceLedgerConnect
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.ReleaseTrace

/-!
Concept: scope-lifetime-finalization R11.
Consumer: original Workers registration and Atomic cleanup bounds.
The source ledger is an instance of the shared place-ledger law (`PlaceFunding.Local`): its
decision and history lifts carry the source configuration and its numeric budget.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program Effect4.Run

/-- **The source ledger's local facts**: the shared place-ledger law then carries its funding
through every command, edit, reply, decision and admitted history.
Consumers: `decision_budget` and `history_budget`. -/
theorem source_local (root : NativeEff) (q : List Nat) (fragment : Fragment root)
    (clearFin : ClearFinalizers root q) (clearLoop : ClearLoops root q) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root) :
    PlaceFunding.Local (PlaceLedgerConnect.source root q) (fun code => current root q code = 0)
      root table where
  control := source_control root q
  quiet := source_no_queue root q
  events := source_events root q
  stores := source_stores root q table
  admin := source_administration root q table
  evaluation := source_evaluation root q fragment clearFin clearLoop table sequential raceFree
  inputs := fun m command owned head => source_inputs root q m command raceFree owned head
  clock := fun _ _ => Nat.le_refl _
  prepare := fun _ _ _ _ => Nat.le_refl _

/-- Every actual decision retains the combined recorded and live source budget, through the
shared place-ledger decision lift. Consumer: `FinalizerRun.census_pushes_once`. -/
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
  have facts := source_local root q fragment clearFin clearLoop table sequential raceFree
  obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift (facts.decision_lift cap fragment)
    fuel () m decision ⟨owned, ledger, (PlaceLedgerConnect.source_funded root q cap m).mpr bounded⟩
    trivial
  exact ⟨moved.1, moved.2.1, (PlaceLedgerConnect.source_funded root q cap _).mp moved.2.2⟩

/-- The original admitted-history carrier retains at most one selected source opportunity,
through the shared place-ledger history law (`PlaceFunding.Local.history_funded`).
The source restrictions are discharged by the actual Atomic and Workers programs.
This invariant establishes neither progress nor arbitrary-source control linearity. -/
theorem history_budget (b : Api.Built) (q : List Nat) (fragment : Fragment b.program)
    (clearFin : ClearFinalizers b.program q) (clearLoop : ClearLoops b.program q)
    (sequential : SequentialSource b.program) (raceFree : RaceFreeSource b.program)
    (compileFuel : Nat) (m : NativeMachine) (history : HistoryOf b compileFuel m) :
    recorded q m + fibers b.program q m ≤ 1 := by
  have funded := PlaceFunding.Local.history_funded b
    (source_local b.program q fragment clearFin clearLoop b.table sequential raceFree) 1 fragment
    compileFuel ((PlaceLedgerConnect.source_funded b.program q 1 _).mpr
      (load_budget b.program q compileFuel)) m history
  exact (PlaceLedgerConnect.source_funded b.program q 1 m).mp funded

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
