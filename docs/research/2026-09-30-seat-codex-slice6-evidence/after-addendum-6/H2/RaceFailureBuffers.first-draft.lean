import Effect4.Laws.Program.Typed.Assembly

/-! Draft for root-controlled checking after RacePayload.failures is strengthened.
The old whole race-payload predicate below retains every proposed H2 field, except that
its failure buffer uses the original FitsCause. No machine reachability is asserted. -/
set_option autoImplicit false
namespace H2RaceFailureBuffers
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def unitTy : EffTy := EffTy.pure .unit
def program : NativeEff := .succeed (.lit .unit)
def child : FiberId := ⟨1⟩
def world : W :=
  { initialWorld unitTy with
    Γ := fun _ => some unitTy
    Θ := fun _ _ => some unitTy }

def race (cause : CauseV) : RRace where
  id := 0
  host := Api.root
  token := 0
  state := {
    unstarted := []
    starting := none
    live := [child]
    remaining := 1
    failures := cause.reasons
    winner := none
    accepted := none
    cleanupNeeded := false
    requests := []
    cleanup := none
    cleanupRequested := false }
  settled := false
  programs := []
  registering := false

/-- The exact pre-fix race payload clauses from the five-source candidate. -/
structure OldRacePayload (root : ProgramSource) (w : W) (r : RRace)
    (resultTy : EffTy) : Prop where
  token : w.Θ r.host r.token = some resultTy
  failures : FitsCause w resultTy.error ⟨r.state.failures⟩
  winner : ∀ pair ∈ r.state.winner, Fits w pair.2 resultTy.answer
  accepted : ∀ exit ∈ r.state.accepted, ExitOk w resultTy exit
  cleanup : ∀ wait ∈ r.state.cleanup, ExitOk w resultTy wait.result
  live : ∀ id ∈ r.state.live, ∀ childTy, w.Γ id = some childTy →
    childTy.answer.sub resultTy.answer = true ∧ childTy.error.sub resultTy.error = true
  programs : ∀ code ∈ r.programs, ∃ childTy, TypedProg root w childTy code ∧
    childTy.answer.sub resultTy.answer = true ∧ childTy.error.sub resultTy.error = true

theorem old_admitted (cause : CauseV) (clean : cleanExit (.failure cause) = true) :
    OldRacePayload (program : ProgramSource) world (race cause) unitTy := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fitsExit_failure_iff world unitTy cause).mp
      (fitsExit_of_clean world unitTy cause clean)
  · intro pair member; cases member
  · intro exit member; cases member
  · intro wait member; cases member
  · intro id member childTy declared
    change some unitTy = some childTy at declared
    cases declared
    exact ⟨Ty.sub_refl _, Ty.sub_refl _⟩
  · intro code member; cases member

theorem old_badName_admitted :
    OldRacePayload (program : ProgramSource) world (race (Cause.die .badName)) unitTy :=
  old_admitted _ rfl

theorem old_notImplemented_admitted :
    OldRacePayload (program : ProgramSource) world (race (Cause.die .notImplemented)) unitTy :=
  old_admitted _ rfl

theorem new_badName_refused :
    ¬ RacePayload (program : ProgramSource) world (race (Cause.die .badName)) unitTy := by
  intro typed
  have excluded := typed.failures.2 (.die .badName .empty) (List.mem_singleton_self _)
  exact excluded.1 rfl

theorem new_notImplemented_refused :
    ¬ RacePayload (program : ProgramSource) world (race (Cause.die .notImplemented)) unitTy := by
  intro typed
  have excluded := typed.failures.2 (.die .notImplemented .empty) (List.mem_singleton_self _)
  exact excluded.2 rfl

theorem new_admitted (cause : CauseV) (typed : ExitOk world unitTy (.failure cause)) :
    RacePayload (program : ProgramSource) world (race cause) unitTy := by
  refine ⟨rfl, typed, ?_, ?_, ?_, ?_, ?_⟩
  · intro pair member; cases member
  · intro exit member; cases member
  · intro wait member; cases member
  · intro id member childTy declared
    change some unitTy = some childTy at declared
    cases declared
    exact ⟨Ty.sub_refl _, Ty.sub_refl _⟩
  · intro code member; cases member

theorem user_die_admitted (value : Nat) :
    RacePayload (program : ProgramSource) world (race (Cause.die (.user value))) unitTy := by
  apply new_admitted
  refine ⟨fitsExit_of_clean world unitTy _ rfl, ?_⟩
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst reason
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem interrupt_admitted :
    RacePayload (program : ProgramSource) world (race (Cause.interrupt none)) unitTy := by
  apply new_admitted
  refine ⟨fitsExit_of_clean world unitTy _ rfl, ?_⟩
  intro reason member
  change reason ∈ [.interrupt none .empty] at member
  rw [List.mem_singleton] at member
  subst reason
  trivial

theorem missingService_admitted :
    RacePayload (program : ProgramSource) world (race (Cause.die .missingService)) unitTy := by
  apply new_admitted
  refine ⟨fitsExit_of_clean world unitTy _ rfl, ?_⟩
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst reason
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- The final child can contribute an empty, admitted cause; settlement still publishes all
previously buffered reasons. Thus checking only the new callback exit cannot close the hole. -/
theorem raceComplete_packages_buffer (cause : CauseV) :
    (Supervision.raceComplete (race cause).state child (.failure Cause.empty)).accepted =
      some (.failure cause) := by
  rw [Supervision.raceComplete_failure_last (race cause).state child Cause.empty
    (List.mem_singleton_self _) rfl (Nat.le_refl 1)]
  change some (.failure ⟨cause.reasons ++ []⟩) = some (.failure cause)
  rw [List.append_nil]

theorem last_empty_failure_typed : ExitOk world unitTy (.failure Cause.empty) :=
  ⟨fitsExit_of_clean world unitTy _ rfl, fun _ member => nomatch member⟩

theorem raceComplete_publishes_badName :
    (Supervision.raceComplete (race (Cause.die .badName)).state child
      (.failure Cause.empty)).accepted = some (.failure (Cause.die .badName)) :=
  raceComplete_packages_buffer _

theorem raceComplete_publishes_notImplemented :
    (Supervision.raceComplete (race (Cause.die .notImplemented)).state child
      (.failure Cause.empty)).accepted = some (.failure (Cause.die .notImplemented)) :=
  raceComplete_packages_buffer _

#print axioms old_admitted
#print axioms old_badName_admitted
#print axioms old_notImplemented_admitted
#print axioms new_badName_refused
#print axioms new_notImplemented_refused
#print axioms new_admitted
#print axioms user_die_admitted
#print axioms interrupt_admitted
#print axioms missingService_admitted
#print axioms raceComplete_packages_buffer
#print axioms last_empty_failure_typed
#print axioms raceComplete_publishes_badName
#print axioms raceComplete_publishes_notImplemented
end H2RaceFailureBuffers
