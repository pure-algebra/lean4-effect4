import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT015SubstitutedDelivery

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that delivers substituted bytes as a successful load —
verification skipped, an altered payload cached and returned as if it
were the admitted node. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .fromWire id (.ok _ bytes) =>
    match s.inFlight[id]? with
    | some (.loading key) =>
        { result := .delivered key (bytes ++ [0])
          state := { s with inFlight := s.inFlight.erase id
                            cache := s.cache.insert key }
          commands := []
          decisions := [(id, .verified key), (id, .cached key),
                        (id, .returned key)] }
    | _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT015_SubstitutedDelivery"
  attacks := "RMT-015"
  represents := "Killing this mutant demonstrates the vectors notice a client that delivers substituted bytes as a successful load — a successful remote load must deliver exactly the canonical encoding of the node the logical admitted-node load holds at that address."
  mutant := mutantStep

end Effects.Mutants.RMT015SubstitutedDelivery
