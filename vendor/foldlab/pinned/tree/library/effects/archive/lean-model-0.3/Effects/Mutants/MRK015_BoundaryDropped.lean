import Effects.Conformance.ManifestMerkle
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.MRK015BoundaryDropped

open Effects.Merkle Effects.Conformance Effects.Conformance.Manifest

/-- A parser that drains every transport fragment in isolation,
discarding the partial-frame remainder at each fragment boundary
instead of carrying it forward. -/
def mutantFeed : FeedFn := fun frags =>
  frags.foldl
    (fun acc frag => acc.bind fun p =>
      (drain frag).map fun q => (p.1 ++ q.1, q.2))
    (some ([], []))

def mutant : Mutant FeedFn where
  id := "MRK015_BoundaryDropped"
  attacks := "MRK-015"
  represents := "Killing this mutant demonstrates the vectors notice a framer that treats every network fragment as a fresh parse — the partial frame carried across a boundary is dropped, so any split inside a length prefix, payload, or address changes what such an implementation reads."
  mutant := mutantFeed

end Effects.Mutants.MRK015BoundaryDropped
