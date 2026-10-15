import Effect4.Laws.Program.FinalizerSource
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.ReleaseTrace

/-!
Concept: scope-lifetime-finalization, R11.
Question: the nonzero race place of `FinalizerRun.once_placed_outside_census`.
Consumer: the joint selected-source command invariant.
Reach: actual race-launch commands with distinct race identities.
Launching transfers the first unlaunched program into its spawned fiber.
This establishes one command balance, with no whole-history or progress claim.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerPlaces
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

abbrev SourceModel := FrameWeights.Model EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceEvent := FrameEvent EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceRace := Race EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev SourceCommand := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev SourceTask := Task EffName EffThunk Val Err Defect FiberId Ann

/-- Existing frame, race and detached program places use one supplied scalar model. -/
def ledger (model : SourceModel) (consume produce : SourceEvent → Nat) :
    PlaceLedger EffName EffThunk Val Err Defect FiberId Ann Ctx Stores where
  fiber := fun fiber => FrameWeights.frame model fiber.frame
  race := fun race => (race.programs.map model.current).sum
  state := fun _ => 0
  command := fun | .resume _ _ code => model.current code | _ => 0
  task := fun | .resume _ _ code => model.current code | _ => 0
  consumed := fun | .frame _ event => consume event | _ => 0
  produced := fun | .frame _ event => produce event | _ => 0

/-- The existing machine's active, saved and unlaunched source reservations. -/
def machineHeld (model : SourceModel) (machine : NativeMachine) : Nat :=
  (machine.fibers.map fun fiber => FrameWeights.frame model fiber.frame).sum +
    (machine.races.map fun race => (race.programs.map (model.current)).sum).sum

/-- One keyed race replacement changes exactly its unlaunched program reservations. -/
theorem update_race_held (model : SourceModel) (machine : NativeMachine)
    (old next : SourceRace) (unique : (machine.races.map Race.id).Nodup)
    (found : machine.race? old.id = some old) (key : next.id = old.id) :
    machineHeld model (machine.updateRace next) + (old.programs.map (model.current)).sum =
      machineHeld model machine + (next.programs.map (model.current)).sum := by
  have changed := ControlWeights.replace_sum Race.id
    (fun race : SourceRace => (race.programs.map (model.current)).sum)
    old next key machine.races unique (List.mem_of_find?_eq_some found)
  simpa only [machineHeld, RunMachine.updateRace, Nat.add_assoc] using
    congrArg (fun n => (machine.fibers.map fun fiber => FrameWeights.frame model fiber.frame).sum + n) changed

/-- Administrative trace emission leaves the concrete source machine places unchanged. -/
theorem machineHeld_emit (model : SourceModel) (machine : NativeMachine)
    (events : List ReleaseTrace.Event) :
    machineHeld model (machine.emit events) = machineHeld model machine := by
  cases events <;> rfl

/-- A native spawn adds exactly the program reservation held by its new fiber. -/
theorem spawn_held (root : NativeEff) (table : RowTable) (model : SourceModel)
    (machine : NativeMachine) (host : SourceFiber) (code : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) :
    machineHeld model (spawn (interpOf root table) machine host code options site).1 =
      machineHeld model machine + model.current code := by
  rw [spawn_machine (site := site), machineHeld_emit]
  simp only [machineHeld, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, spawnedChild, FrameWeights.frame, RunFiber.make, FrameFiber.start,
    Nat.add_zero]
  omega

/-- Launching transfers the entrant reservation from the race into its actual spawned fiber.
The real pending commands and detached snapshot remain part of the ledger. -/
theorem launch_balance (root : NativeEff) (table : RowTable) (model : SourceModel)
    (consume produce : SourceEvent → Nat)
    (machine : NativeMachine) (raceId : Nat) (rest : List SourceCommand)
    (snapshot : List SourceTask) (unique : (machine.races.map Race.id).Nodup) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) machine (.launch raceId) rest
    (ledger model consume produce).Balanced machine (.launch raceId :: rest) snapshot out.1 out.2 snapshot := by
  letI := evaluatorFor root table
  cases found : machine.race? raceId with
  | none =>
    simp only [driveStep, found, PlaceLedger.Balanced, PlaceLedger.spent, PlaceLedger.held,
      PlaceLedger.issued, ledger, List.map_cons, List.sum_cons, Nat.zero_add, Nat.le_refl]
  | some race =>
    cases programs : race.programs with
    | nil =>
      simp only [driveStep, found, programs, PlaceLedger.Balanced, PlaceLedger.spent, PlaceLedger.held,
        PlaceLedger.issued, ledger, List.map_cons, List.sum_cons, Nat.zero_add, Nat.le_refl]
    | cons code more =>
      simp only [driveStep, found, programs]
      split
      · simp only [PlaceLedger.Balanced, PlaceLedger.spent, PlaceLedger.held,
          PlaceLedger.issued, ledger, List.map_cons, List.sum_cons, Nat.zero_add, Nat.le_refl]
      · cases lookup : machine.fiber? race.host with
        | none =>
          simp only [PlaceLedger.Balanced, PlaceLedger.spent, PlaceLedger.held,
            PlaceLedger.issued, ledger, List.map_cons, List.sum_cons, Nat.zero_add, Nat.le_refl]
        | some host =>
          let born := launchEntrant (interpOf root table) raceId machine host code (race.nextSite.getD [])
          let next : SourceRace := {race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1])}
          have raceFound : born.1.race? race.id = some race := by
            change machine.race? race.id = some race
            simpa only [race_id_of_lookup found] using found
          have changed := update_race_held model born.1 race next unique raceFound rfl
          have added := spawn_held root table model machine host code
            ⟨true, true, .interruptible⟩ (race.nextSite.getD [])
          change machineHeld model born.1 = machineHeld model machine + model.current code at added
          rw [programs, show next.programs = more from rfl, List.map_cons, List.sum_cons] at changed
          have heldEq : machineHeld model (born.1.updateRace next) = machineHeld model machine := by omega
          have trace : ((born.1.updateRace next).emit [.raceLaunched raceId born.2]).trace =
              machine.trace ++ [.forked host.id ⟨machine.nextId⟩ true, .raceLaunched raceId born.2] := by
            change ((spawn (interpOf root table) machine host code ⟨true, true, .interruptible⟩ _).1.emit _).trace = _
            rw [spawn_machine (site := race.nextSite.getD []), RunMachine.emit_trace, RunMachine.emit_trace]
            change machine.trace ++ [.forked host.id ⟨machine.nextId⟩ true] ++
              [.raceLaunched raceId born.2] = _
            exact List.append_assoc _ _ _
          have finalHeld : machineHeld model ((born.1.updateRace next).emit [.raceLaunched raceId born.2]) =
              machineHeld model machine := (machineHeld_emit _ _ _).trans heldEq
          change (ledger model consume produce).Balanced machine (.launch raceId :: rest) snapshot
            ((born.1.updateRace next).emit [.raceLaunched raceId born.2])
            (.evaluate born.2 :: .enrollRace raceId born.2 :: .launch raceId :: rest) snapshot
          unfold PlaceLedger.Balanced PlaceLedger.spent PlaceLedger.issued PlaceLedger.held
          simp only [ledger, List.map_cons, List.sum_cons, Nat.zero_add, trace,
            List.map_append, List.sum_append, List.map_nil, List.sum_nil,
             Nat.add_zero]
          change (machine.trace.map (fun | .frame _ event => consume event | _ => 0)).sum +
            (machineHeld model ((born.1.updateRace next).emit [.raceLaunched raceId born.2]) +
              (rest.map (fun | .resume _ _ code => model.current code | _ => 0)).sum +
              (snapshot.map (fun | .resume _ _ code => model.current code | _ => 0)).sum) + _ ≤
            _ + (machineHeld model machine + _ + _) + _
          rw [finalHeld]
          exact Nat.le_refl _

end Effect4.Program.FinalizerPlaces
