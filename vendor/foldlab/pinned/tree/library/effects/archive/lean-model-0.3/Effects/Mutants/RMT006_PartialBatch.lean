import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT006PartialBatch

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that skips batch accounting: any batch result is folded
into the planning sets, misaligned, short, or reordered as it may be. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .fromWire id (.batchResult results) =>
    match s.inFlight[id]? with
    | some (.findingMissing _) =>
        let noted :=
          notePresence { s with inFlight := s.inFlight.erase id } results
        { result := .batchAnswered noted.2.1 noted.2.2
          state := noted.1
          commands := []
          decisions := [(id, .presenceNoted noted.2.1 noted.2.2)] }
    | _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT006_PartialBatch"
  attacks := "RMT-006"
  represents := "Killing this mutant demonstrates the vectors notice a client that applies a misaligned batch answer instead of failing the whole batch closed — per-key answers partially applied and substituted across keys."
  mutant := mutantStep

end Effects.Mutants.RMT006PartialBatch
