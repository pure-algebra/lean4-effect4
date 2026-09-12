import Effect4.Api
import Effect4.Laws.Machine.Approximation

/-! A finished replay is unchanged by a larger command budget when its
compile budget and all explicit inputs remain fixed. -/
set_option autoImplicit false
namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program

/-- DI-68: driver stability lifts to equality of the whole public run,
including its store, trace and observed reasons. -/
theorem finished_mono_fuel (p : Api.Program) (f f' : Nat)
    (tape : List Api.Decision) (choices : List Bool)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable) (cf : Nat)
    (h : (Api.replay p f tape choices answers table cf).outcome = .finished)
    (hle : f ≤ f') :
    Api.replay p f' tape choices answers table cf = Api.replay p f tape choices answers table cf := by
  letI := evaluatorFor p table
  have ht : (replayEval (interpOf p table) f tape (Api.load p cf choices answers)).terminal = true := by
    cases hr : replayEval (interpOf p table) f tape (Api.load p cf choices answers) <;>
      simp [Api.replay, hr, ReplayResult.terminal] at h ⊢
  have hs := Suffices_of_replay_terminal (interpOf p table) f tape
    (Api.load p cf choices answers) ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold Api.replay
  rw [replay_stable (interpOf p table) f tape (Api.load p cf choices answers) hs k]

#print axioms finished_mono_fuel
end Effect4.Api
