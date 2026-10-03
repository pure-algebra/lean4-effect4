import Effect4.Laws.Api.Runner

/-!
# The runner's behaviour is the only map that unfolds along `step`: controls

Controls for `behaviour_unique` (`src/Effect4/Laws/Api/Runner.lean`; formal pass, algebra note
A7, probe `P3TapeAction.lean`). Positive: the phases `replayPlay` writes satisfy the two
unfolding equations, so they are `behaviour`. Red: the first equation alone does not pin
`behaviour`; the map that observes nothing satisfies it and differs on every one-row journal
(`behaviour_needs_cons`), and the uniqueness law refuses that map at its second equation (pinned
below). This is the session runner's law (coherence census row 27), not the run observations'
missing finality (row 38 of the same census).
-/

set_option autoImplicit false
namespace Test.Api.RunnerFinality
open Effect4.Api.Runner

/-- The map that observes nothing. -/
def silent : Runner → List Command → List Effect4.Api.HostSession.Phase := fun _ _ => []

/-- The phases a journal's play writes are the runner's behaviour. -/
theorem replayPlay_phases (journal : List Command) (p : Runner) :
    (replayPlay journal p).2 = behaviour p journal :=
  behaviour_unique (fun p j => (replayPlay j p).2) (fun _ => rfl) (fun _ _ _ => rfl) journal p

/-- **Red control: `behaviour_nil` does not pin `behaviour`.** `silent` satisfies the first
unfolding equation and differs from `behaviour` on every one-row journal. -/
theorem behaviour_needs_cons :
    (∀ p, silent p [] = []) ∧ ∀ p c, silent p [c] ≠ behaviour p [c] := by
  refine ⟨fun _ => rfl, fun p c h => ?_⟩
  rw [behaviour_cons] at h
  cases h

/-! The uniqueness law refuses `silent` at its second equation. -/

/--
error: Type mismatch
  rfl
has type
  ?m.11 = ?m.11
but is expected to have type
  silent x✝² (x✝¹ :: x✝) = (step x✝² x✝¹).snd :: silent (step x✝² x✝¹).fst x✝
-/
#guard_msgs (error) in
example : ∀ journal p, silent p journal = behaviour p journal :=
  behaviour_unique silent (fun _ => rfl) (fun _ _ _ => rfl)

end Test.Api.RunnerFinality
