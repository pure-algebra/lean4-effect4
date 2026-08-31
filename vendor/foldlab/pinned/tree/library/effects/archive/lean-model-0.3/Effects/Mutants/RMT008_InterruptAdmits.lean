import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT008InterruptAdmits

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that treats an interrupted upload as a completed one:
the key is admitted and confirmed on the strength of an operation
that never finished. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .fromWire id .interrupted =>
    match s.inFlight[id]? with
    | some (.uploading key _bytes) =>
        { result := .uploaded key
          state := { s with inFlight := s.inFlight.erase id,
                            cache := s.cache.insert key,
                            confirmed := s.confirmed.insert key }
          commands := []
          decisions := [(id, .cached key)] }
    | _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT008_InterruptAdmits"
  attacks := "RMT-008"
  represents := "Killing this mutant demonstrates the vectors notice a client that admits and confirms a key at an interruption point — semantic residue from an operation that never completed."
  mutant := mutantStep

end Effects.Mutants.RMT008InterruptAdmits
