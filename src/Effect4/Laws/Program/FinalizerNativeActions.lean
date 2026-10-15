import Effect4.Laws.Program.FinalizerScopes
import Effect4.Laws.Program.FinalizerControl
import Effect4.Laws.Program.PlaceFunding.Actions

/-!
Concept: scope-lifetime-finalization R11.
Question: actual action debit serves FinalizerRun.once_placed_outside_census.
Consumer: the full source primitive and command accounting.
Races receive the reservation of their actual unlaunched programs.
Parallel finalizers carry release custody and add zero active source weight.
These local bounds establish no whole-history funding or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Native action answers and administrative saved frames have zero source weight. -/
theorem actionInputs (root : NativeEff) (q : List Nat) (view) (table : RowTable) :
    WriterWeights.ActionInputs (frameModel root q) (interpAt root view table) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- The recorded nested-command certificate excludes resume-program weight from actual action commands. -/
theorem action_commands_zero (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (action : NAction) :
    ((evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action).nested.map
      (ledger root q).command).sum = 0 := by
  apply PlaceFunding.nested_zero (ledger root q).command
    (root := root) (table := table) (next := evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action)
  · intro command held
    cases command
    case resume => exact held.elim
    all_goals rfl
  · intro owner command held
    cases command
    case resume => exact held.elim
    all_goals rfl
  · intro race; rfl
  · intro race yielding; rfl
  · exact Guard.ReturnCommands.withFiber_nested root table (interpAt root view table) machine fiber yielding action

/-- A race transfers its actual entrant reservation from the returned parent into the race row. -/
theorem begin_race_debit (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (programs : List NCode) (site : Option (List Nat)) (mode : Supervision.RaceMode)
    (carried : (programs.map (current root q)).sum ≤ current root q fiber.frame.current) :
    (ledger root q).IterDebit machine fiber
      (beginRace (interpAt root view table) machine fiber yielding programs site mode) := by
  let next := beginRace (interpAt root view table) machine fiber yielding programs site mode
  have trace := (events root q).trace_debit
    (show Moves.AdministrativeTrace machine next.machine from
      ⟨[.raceStarted machine.nextRace fiber.id programs.length], (by rfl), RunMachine.emit_trace _ _⟩)
  have outside : (ledger root q).outside fiber.id next.machine next.nested =
      (ledger root q).outside fiber.id machine [] + (programs.map (current root q)).sum := by
    simp only [next, PlaceLedger.outside, beginRace, RunMachine.emit, ledger, FiberSum.outside,
      List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    omega
  have own : (ledger root q).fiber next.fiber = (fiber.frame.stack.map (saved root q)).sum := by
    change 0 + _ = _
    exact Nat.zero_add _
  change (ledger root q).IterDebit machine fiber next
  unfold PlaceLedger.IterDebit
  rw [outside, own]
  change _ ≤ (ledger root q).spent machine + (ledger root q).outside fiber.id machine [] +
    (current root q fiber.frame.current + (fiber.frame.stack.map (saved root q)).sum) +
      (ledger root q).issued next.machine
  omega

/-- Every non-parallel action supplies the existing frame-local program bound. -/
theorem ordinary_carried (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (action : NAction)
    (scopes : ScopesAt q machine.state.scopes)
    (carried : actionWeight root q action ≤ current root q fiber.frame.current)
    (ordinary : ∀ programs, action ≠ .closePar programs) :
    WriterWeights.Carried (frameModel root q) (interpAt root view table) machine fiber action := by
  cases action
  case fork | forkIn | forkScoped | setInterruptible => exact carried
  case closeScope scope exit =>
    intro state program closed
    exact close_native_zero root q view table scope exit fiber.frame.interruptible fiber.id
      machine.state state program scopes closed
  case closePar programs => exact ordinary programs rfl
  all_goals trivial

/-- The complete actual action retains its source reservation, including races and parallel closes. -/
theorem action_debit (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (suspended : EffThunk) (action : NAction) (scopes : ScopesAt q machine.state.scopes)
    (selected : fiber.frame.current = .withFiber suspended) (held : ThunkAt q suspended)
    (found : (interpAt root view table).withFiberOf suspended = some action) :
    (ledger root q).IterDebit machine fiber
      (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding action) := by
  have carried : actionWeight root q action ≤ current root q fiber.frame.current := by
    rw [selected]
    exact interp_action_le root q view table suspended action held found
  have localBound (next : NAction)
      (bounded : WriterWeights.LocalBound (frameModel root q) machine fiber
        (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding next))
      (first : ∀ programs site, next ≠ .raceAll programs site)
      (last : ∀ programs site, next ≠ .raceAllFirst programs site) :
      (ledger root q).IterDebit machine fiber
        (evaluatePrim.withFiber (interpAt root view table) machine fiber yielding next) := by
    apply PlaceFunding.bound_debit_places (events root q) (frameModel root q) (fun _ => rfl)
      machine fiber _ bounded
      (PlaceFunding.withFiber_administrative (interpAt root view table) machine fiber yielding next)
      (Nat.le_refl _)
    · rw [PlaceFunding.with_fiber_races (interpAt root view table) machine fiber yielding next first last]
      exact Nat.le_refl _
    · exact action_commands_zero root q view table machine fiber yielding next
  cases action
  case raceAll programs site => exact begin_race_debit root q view table machine fiber yielding programs site .firstSuccess carried
  case raceAllFirst programs site => exact begin_race_debit root q view table machine fiber yielding programs site .firstExit carried
  case closePar programs =>
    exact localBound _ (WriterWeights.parallel_bound (frameModel root q) (interpAt root view table)
      machine fiber yielding programs (interp_parallel_zero root q view table suspended programs held found))
      (fun _ _ impossible => nomatch impossible) (fun _ _ impossible => nomatch impossible)
  all_goals
    apply localBound _
      (WriterWeights.action_bound (frameModel root q) (interpAt root view table) (actionInputs root q view table)
        machine fiber yielding _ (ordinary_carried root q view table machine fiber _ scopes carried
          (fun _ impossible => nomatch impossible)))
      (fun _ _ impossible => nomatch impossible) (fun _ _ impossible => nomatch impossible)

end Effect4.Program.FinalizerSource
