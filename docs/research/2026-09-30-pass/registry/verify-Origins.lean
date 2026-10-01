import Effect4.Laws.Program.RuntimeR

/-! Verifier of the registry seat: the reference machine records the same creation sites.

Research evidence outside the Test root. Base `be15b062`. Written by the adversarial verifier.

The seat left open whether the reference evaluator's fork sites (`Laws/Program/EvaluateR.lean`)
match the native machine's (note §11). They do, on every tape: the proved book relation
(`replay_rel`, `RuntimeR.lean:162`) relates the two replays fiber by fiber, and related
fibers have one origin (`FMeans.origin`, `Laws/Program/Simulation/Fibers.lean:67`). So a
registry read off `RunFiber.origin` answers the same on both machines, which is what the
proof-side `RegistryAgrees` needs. The theorem is at the empty table, like `run_eq_ref`. -/

set_option autoImplicit false

namespace Research.Pass.RegistryVerify.Origins
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- Every fiber id has the same origin (root, or parent, daemon flag and site) on the native
replay and on the reference replay of the same program and tape. -/
theorem origin_eq_ref (e : NativeEff) (fuel : Nat) (tape : List Api.Decision) (id : FiberId) :
    ((Api.replay e fuel tape).machine.fiber? id).map (·.origin) =
      ((replayR e fuel tape).machine.fiber? id).map (·.origin) := by
  rw [replay_machine]
  rcases BMeans.fiber?_cases (ReplayRel.machine (replay_rel e fuel fuel tape)) id with
    ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · have h₂' : (replayR e fuel tape).machine.fiber? id = none := h₂
    rw [h₁, h₂']
    rfl
  · have h₂' : (replayR e fuel tape).machine.fiber? id = some f₂ := h₂
    rw [h₁, h₂']
    exact congrArg some (FMeans.origin hf)

#print axioms origin_eq_ref

end Research.Pass.RegistryVerify.Origins
