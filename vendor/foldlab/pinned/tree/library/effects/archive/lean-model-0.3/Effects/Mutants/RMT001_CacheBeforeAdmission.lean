import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT001CacheBeforeAdmission

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that caches and returns whatever the wire answered for an
in-flight load, verification be damned. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .fromWire id (.ok _ bytes) =>
    match s.inFlight[id]? with
    | some (.loading key) =>
        { result := .delivered key bytes
          state := { s with inFlight := s.inFlight.erase id, cache := s.cache.insert key }
          commands := []
          decisions := [(id, .cached key), (id, .returned key)] }
    | _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT001_CacheBeforeAdmission"
  attacks := "RMT-001"
  represents := "Killing this mutant demonstrates the vectors notice a client that caches and returns un-verified wire bytes — a wire-supplied digest treated as an identity instead of a routing hint."
  mutant := mutantStep

end Effects.Mutants.RMT001CacheBeforeAdmission
