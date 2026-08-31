import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT005PresenceAdmits

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that treats a batch answer's `found` keys as admission:
whatever the server claims to hold lands in the local cache, wire
bytes unverified. -/
def mutantStep : RStep := fun s i =>
  let o := Effects.Remote.step vecParams s i
  match i with
  | .fromWire id (.batchResult results) =>
    match s.inFlight[id]? with
    | some (.findingMissing _) =>
        { o with state := { o.state with
            cache := results.foldl
              (fun c r => match r with
                | .found key _ => c.insert key
                | _ => c) o.state.cache } }
    | _ => o
  | _ => o

def mutant : Mutant RStep where
  id := "RMT005_PresenceAdmits"
  attacks := "RMT-005"
  represents := "Killing this mutant demonstrates the vectors notice a client that turns presence reports into admission — a server's claim to hold a key populating the cache without any verified bytes ever arriving."
  mutant := mutantStep

end Effects.Mutants.RMT005PresenceAdmits
