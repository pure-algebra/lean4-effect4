import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RPL002LiveFallback

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- On a replay rejection, additionally request live delegation — the
forbidden fallback. -/
def mutantReduce : RReducer := fun s i =>
  let o := reduce s i
  match s.mode, o.result with
  | .replay, .rejected _ _ =>
      { o with decisions := o.decisions ++ [.liveDelegation "fallback" s.cursor] }
  | _, _ => o

def mutant : Mutant RReducer where
  id := "RPL002_LiveFallback"
  attacks := "RPL-002"
  represents := "Killing this mutant demonstrates the vectors notice a replay mismatch falling through to a live adapter — the decision trace, not a separate oracle, is what convicts the fallback."
  mutant := mutantReduce

end Effects.Mutants.RPL002LiveFallback
