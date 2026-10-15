import Effect4.Laws.Program.FinalizerNativeActions
import Effect4.Laws.Program.FinalizerNativeFrames
import Effect4.Laws.Program.NativeReplies

/-!
Concept: scope-lifetime-finalization R11.
Question: actual primitive debit serves FinalizerRun.once_placed_outside_census.
Consumer: full native execution and its command accounting.
The existing primitive producer covers every evaluator result once.
Actual cancellation slots, race rows and pending program places remain explicit.
This local debit establishes neither complete history funding nor progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Registration changes race metadata while retaining its actual unlaunched reservation. -/
theorem register_race_debit (root : NativeEff) (q : List Nat) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (raceId : Nat)
    (unique : (machine.races.map Race.id).Nodup) :
    (ledger root q).IterDebit machine fiber (registerRace machine fiber yielding raceId) := by
  unfold registerRace
  cases found : machine.race? raceId with
  | none => exact Nat.le_refl _
  | some race =>
    have actual : machine.race? race.id = some race := by
      simpa only [Guard.race_id_of_lookup found] using found
    have changed := ControlWeights.replace_sum Race.id
      (fun row : FinalizerPlaces.SourceRace => (row.programs.map (current root q)).sum)
      race {race with registering := true} rfl machine.races unique (List.mem_of_find?_eq_some actual)
    have equal : ((machine.updateRace {race with registering := true}).races.map
        (fun row => (row.programs.map (current root q)).sum)).sum =
        (machine.races.map (fun row => (row.programs.map (current root q)).sum)).sum := by
      exact Nat.add_right_cancel changed
    unfold PlaceLedger.IterDebit PlaceLedger.outside
    simp only [ledger, RunMachine.updateRace, PlaceLedger.spent, PlaceLedger.issued, FiberSum.outside,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add, Nat.add_zero]
    dsimp only [RunMachine.updateRace] at equal
    rw [equal]
    exact Nat.le_refl _

/-- Actual countdown parking spends no new source reservation or unlaunched race program. -/
theorem countdown_debit (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (targets : List FiberId) :
    let out := countdownParkEdits (interpAt root view table) machine fiber targets .exitsValue false
    (ledger root q).IterDebit machine fiber ⟨out.1, out.2.1, yielding, .continue_, [], out.2.2.2⟩ := by
  have races : (countdownParkEdits (interpAt root view table) machine fiber targets .exitsValue false).1.races =
      machine.races := by
    unfold countdownParkEdits
    dsimp only
    split <;> rfl
  apply PlaceFunding.bound_debit_places (events root q) (frameModel root q) (fun _ => rfl)
    machine fiber _
    (WriterWeights.countdown_plan_bound (frameModel root q) (interpAt root view table)
      (actionInputs root q view table) machine fiber yielding targets .exitsValue false (fun _ => rfl))
    (PlaceFunding.countdown_administrative (interpAt root view table) machine fiber targets .exitsValue false)
    (Nat.le_refl _)
  · rw [races]
    exact Nat.le_refl _
  · rfl

/-- Every actual primitive result retains the selected source reservation at its real places. -/
theorem primitive_debit (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (frames : FrameAt q fiber.frame) (currentAt : TemplateAt q fiber.frame.current)
    (scopes : ScopesAt q machine.state.scopes) (unique : (machine.races.map Race.id).Nodup) :
    (ledger root q).IterDebit machine fiber (evaluatePrim (interpAt root view table) machine fiber yielding) := by
  apply PlaceFunding.primitive_debit_of_drain (L := ledger root q) rfl (control root q) (events root q)
    (interpAt root view table) machine fiber yielding
  refine {
    success := fun _ => rfl, failure := fun _ => rfl,
    exitValue := ?_, step := step_frame_debit root q view table placed machine fiber yielding frames,
    finalizer := fun exit => finalizer_debit root q view table placed machine fiber yielding exit frames,
    action := ?_, sync := ?_, registerState := fun _ _ _ _ _ _ _ => Nat.le_refl _,
    registerReply := ?_, cancel := ?_, joinCancel := ?_, countdown := ?_,
    race := fun race _ => register_race_debit root q machine fiber yielding race unique }
  case refine_1 => intro exit mode; cases exit <;> cases mode <;> rfl
  case refine_2 =>
    intro suspended action selected found
    have owned := currentAt.1
    rw [selected] at owned
    exact action_debit root q view table machine fiber yielding suspended action scopes selected owned found
  case refine_3 =>
    intro suspended state value _ _
    change 0 + (0 + (fiber.frame.stack.map (saved root q)).sum) ≤
      0 + (current root q fiber.frame.current + (fiber.frame.stack.map (saved root q)).sum)
    omega
  case refine_4 =>
    intro register signal cancel state code _ produced
    exact terminal_zero root q code
      (SourceScope.register_reply root view table register fiber.id machine.nextToken machine.state code
        (congrArg Prod.snd produced))
  case refine_5 =>
    intro register signal cancel state selected _
    have owned := currentAt.2.2
    rw [selected] at owned
    have zero : name q ((interpAt root view table).cancelName
        (cancel.getD (interpAt root view table).abortName) fiber.id machine.nextToken) = 0 := by
      cases cancel with
      | none => rfl
      | some callback => exact owned callback rfl
    change current root q fiber.frame.current +
      (name q ((interpAt root view table).cancelName
        (cancel.getD (interpAt root view table).abortName) fiber.id machine.nextToken) +
          (fiber.frame.stack.map (saved root q)).sum) ≤
        current root q fiber.frame.current + (fiber.frame.stack.map (saved root q)).sum
    rw [zero, Nat.zero_add]
    exact Nat.le_refl _
  case refine_6 =>
    change current root q fiber.frame.current + (0 + (fiber.frame.stack.map (saved root q)).sum) ≤
      current root q fiber.frame.current + (fiber.frame.stack.map (saved root q)).sum
    rw [Nat.zero_add]
    exact Nat.le_refl _
  case refine_7 =>
    intro targets next returned parked edits _ counted
    have bounded := countdown_debit root q view table machine fiber yielding targets
    rw [counted] at bounded
    exact bounded

end Effect4.Program.FinalizerSource
