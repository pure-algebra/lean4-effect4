import Effect4.Laws.Program.CodeClosure.ConfigurationEdits
import Effect4.Laws.Program.Simulation.Pending
import Effect4.Laws.Program.NativeFrameRows
import Effect4.Laws.Program.PrimitiveDispatcher
import Effect4.Laws.Program.PlaceFunding.Actions

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: native metadata retains full source annotations without another evaluator proof.
Consumer: the full finalizer instance of the common configuration command transport.
The pending condition reads the existing simulation invariant.
Stored rows and dispatcher tasks use their existing joint producer.
Only actual race entry can introduce new unlaunched programs.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Configuration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- The configuration's countdown condition is the existing simulation condition. -/
theorem pending_iff (model : Model) (fiber : SourceFiber) :
    (∀ pending ∈ fiber.pending, ResumeAt model pending.resumeWith) ↔ PendingOk fiber := by
  constructor
  · intro held pending member callback same
    have allowed := held pending member
    rw [same] at allowed
    exact allowed
  · intro held pending member
    have allowed := held pending member
    cases actual : pending.resumeWith
    case continueWith callback => exact (allowed callback actual).elim
    all_goals trivial

/-- Actual native evaluation reuses the existing proof that no countdown stores a callback. -/
theorem native_pending (model : Model) (root : NativeEff) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (held : ∀ pending ∈ fiber.pending, ResumeAt model pending.resumeWith) :
    ∀ pending ∈ (evaluateNative root machine fiber yielding table).fiber.pending,
      ResumeAt model pending.resumeWith :=
  (pending_iff model _).mpr (Sched.evaluateNative_pendingOk (table := table) root machine fiber yielding
    ((pending_iff model fiber).mp held))

/-- Every actual primitive action shares the stored-row and scheduler producer. -/
theorem primitive_rows_dispatcher (model : Model) (root : NativeEff) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (success : ∀ value, model.code (.success value))
    (rows : ∀ row ∈ machine.fibers, FiberAt model row) (tasks : DispatcherAt model fiber.dispatcher)
    (actions : ∀ thunk action, fiber.frame.current = .withFiber thunk →
      (interpAt root view table).parkOf fiber.frame.current = none →
      (interpAt root view table).withFiberOf thunk = some action →
      ChildProgramsWith model.races True model.code action) :
    let result := evaluatePrim (interpAt root view table) machine fiber yielding
    (∀ row ∈ result.machine.fibers, FiberAt model row) ∧ DispatcherAt model result.fiber.dispatcher := by
  apply Moves.evaluatePrim_dispatcher_on (interpAt root view table) machine fiber yielding
    (fun rows => ∀ row ∈ rows, FiberAt model row) (TaskAt model)
    (fun _ _ => ⟨success _, TerminalReply.success _⟩) rows tasks
  intro thunk action selected unparked found
  apply with_fiber_rows_dispatcher_at (races := model.races) (parallel := True)
    root view table model.code (FiberAt model) (TaskAt model) machine fiber yielding action
    0 (Nat.zero_le _) rows (actions thunk action selected unparked found)
  · intro id _ program flag budget context owned
    exact fiber_make_at model id program flag budget context owned
  · exact tasks
  · intro child; trivial

/-- An action's race rows use its supplied actual entrant programs. -/
theorem action_races (model : Model) (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (action : NAction)
    (rows : ∀ race ∈ machine.races, RaceAt model race)
    (source : ChildProgramsWith model.races True model.code action) :
    ∀ race ∈ (evaluatePrim.withFiber interp machine fiber yielding action).machine.races, RaceAt model race := by
  cases action
  case raceAll programs site | raceAllFirst programs site =>
    intro race member
    rcases List.mem_append.mp member with old | born
    · exact rows race old
    · rw [List.mem_singleton.mp born]
      exact source
  all_goals
    rw [PlaceFunding.with_fiber_races interp machine fiber yielding _
      (by intro programs site same; cases same) (by intro programs site same; cases same)]
    exact rows

/-- Registration updates metadata on the same actual unlaunched programs. -/
theorem register_races (model : Model) (machine : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (raceId : Nat) (rows : ∀ race ∈ machine.races, RaceAt model race) :
    ∀ race ∈ (registerRace machine fiber yielding raceId).machine.races, RaceAt model race := by
  unfold registerRace
  split
  · exact rows
  · rename_i race found
    have held := rows race (List.mem_of_find?_eq_some found)
    intro other member
    obtain ⟨old, present, same⟩ := List.mem_map.mp member
    rw [← same]
    split
    · exact held
    · exact rows old present

/-- The existing primitive producer exposes the only race-row changes. -/
theorem primitive_races (model : Model) (interp : Moves.NInterp)
    (machine : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (rows : ∀ race ∈ machine.races, RaceAt model race)
    (actions : ∀ thunk action, fiber.frame.current = .withFiber thunk → interp.parkOf fiber.frame.current = none →
      interp.withFiberOf thunk = some action →
      ∀ race ∈ (evaluatePrim.withFiber interp machine fiber yielding action).machine.races, RaceAt model race) :
    ∀ race ∈ (evaluatePrim interp machine fiber yielding).machine.races, RaceAt model race := by
  have produced := Moves.evaluatePrim_producer interp machine fiber yielding
  generalize actual : evaluatePrim interp machine fiber yielding = result at produced ⊢
  cases produced with
  | step =>
    obtain ⟨events, frame, outcome, same⟩ := NativeFrameRows.step_frame_only interp machine fiber yielding
    rw [same]
    exact rows
  | finalizer exit =>
    obtain ⟨events, frame, outcome, same⟩ := NativeFrameRows.finalizer_frame_only interp machine fiber yielding exit
    rw [same]
    exact rows
  | action thunk action selected unparked found => exact actions thunk action selected unparked found
  | racePark race park => exact register_races model machine fiber yielding race rows
  | countdownPark targets next returned parked edits park counted =>
    have same : (countdownParkEdits interp machine fiber targets .exitsValue false).1.races = machine.races := by
      unfold countdownParkEdits
      dsimp only
      split <;> rfl
    rw [counted] at same
    cases parked <;> exact same ▸ rows
  | _ => exact rows

end Effect4.Program.CodeClosure.Configuration
