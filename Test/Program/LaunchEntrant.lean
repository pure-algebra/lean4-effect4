import Test.Program.RegistrationColumn
import Effect4.Laws.Program.Typed.Commands.Launch

/-!
# Test.Program.LaunchEntrant — one race entrant's launch keeps `I`

Placement: semantics Concept 4 (`reactive-scheduling`), scheduler step preservation;
`launch_preserves` (`launch_preserves`, `Typed/Commands/Launch.lean`). The input is
RegistrationColumn's typed configuration with one unlaunched entrant program on its race, moved
there by the general race edit (`configTyped_updateRace`), and the two commands `registerRace`
queues (`Machine/Fibers.lean:944`). The actual step takes the allocating arm: it appends the
entrant at the old `nextId`, queues its evaluation and enrollment ahead of the next launch, and the
general theorem types the result at a world that extends the input's.

Reach: one constructed input and one command; the input is not asserted reachable. The control
shows that `launch_preserves`'s premise is inhabited at a configuration whose launch allocates. It
does not prove progress, the entrant's evaluation, or host response.
-/

set_option autoImplicit false

namespace Test.Program.LaunchEntrant
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
open Test.Program.RegistrationColumn (rootProgram natTy world fiber race emptyPayload)

def entrant : RProgram := .pure (.success (.nat 0))

def launchRace : Effect4.Program.Typed.RRace := { race with programs := [entrant] }

def machine : RState := Test.Program.RegistrationColumn.machine.updateRace launchRace

def rest : List RCmd := [.registrationDone 0 false]

theorem entrant_typed (w : Effect4.Program.Typed.World) : TypedProg (rootProgram : ProgramSource) w natTy entrant := by
  refine TypedProg.pure ⟨?_, trivial⟩
  rw [fitsExit_success_iff]
  change Typed.Fits w (Val.nat 0) .nat
  simp only [Typed.Fits]

theorem payload : RacePayload (rootProgram : ProgramSource) world launchRace natTy :=
  emptyPayload world launchRace natTy rfl rfl rfl rfl rfl (fun _ h => nomatch h)
    (fun code hc => by
      rw [show launchRace.programs = [entrant] from rfl, List.mem_singleton] at hc
      subst hc
      exact ⟨natTy, entrant_typed world, Ty.subN_refl _, Ty.subN_refl _⟩)

/-- The race edit keeps RegistrationColumn's typed configuration. -/
theorem tail_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine rest :=
  configTyped_updateRace Test.Program.RegistrationColumn.config_typed (old := race)
    (new := launchRace) rfl rfl rfl rfl payload (fun _ h => .inl h)

/-- The launch `registerRace` queues ahead of the registration's completion. -/
theorem config_typed :
    ConfigTyped (rootProgram : ProgramSource) natTy world machine (.launch 0 :: rest) :=
  ⟨tail_typed.machine,
    readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) tail_typed.code,
    queueOk_cons
      { payload := trivial
        authority := ⟨launchRace, rfl, fiber, rfl, rfl, rfl⟩
        delivery := trivial
        owner := fun _ h => nomatch h
        tail := ⟨false, List.mem_singleton_self _⟩
        keysBelow := fun _ h => nomatch h
        keysFree := fun _ _ _ _ h => nomatch h
        observer := fun _ _ _ h => nomatch h
        enroll := fun _ _ h => nomatch h
        noRace := fun _ _ _ h => nomatch h
        link := fun _ _ _ _ _ h => nomatch h
        raceObservers := fun _ _ _ h => nomatch h } tail_typed.queue⟩

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.launch 0) rest

/-- The actual step allocates: one more fiber at the old `nextId`, its evaluation and enrollment
queued ahead of the next launch, the race's program consumed. -/
theorem allocates :
    result.2 = [.evaluate ⟨1⟩, .enrollRace 0 ⟨1⟩, .launch 0, .registrationDone 0 false] ∧
      result.1.nextId = 2 ∧ result.1.fibers.length = 2 ∧
      (result.1.race? 0).map (·.programs) = some [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The general theorem types the allocating step's result. -/
theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 :=
  launch_preserves (rootProgram : ProgramSource) natTy 0 world machine rest rfl config_typed

end Test.Program.LaunchEntrant
