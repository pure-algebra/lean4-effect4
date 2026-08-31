import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT007PublishUnconfirmed

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that publishes a root without checking that its closure
stands confirmed: the ordering gate is simply skipped. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .request id (.publishRoot key _closure) =>
    match s.inFlight[id]? with
    | none =>
        { result := .commanded
          state := { s with inFlight := s.inFlight.insert id (.publishing key) }
          commands := [(id, .publishRoot key)]
          decisions := [(id, .issued (.publishRoot key))] }
    | some _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT007_PublishUnconfirmed"
  attacks := "RMT-007"
  represents := "Killing this mutant demonstrates the vectors notice a client that publishes a root whose closure never stood confirmed — a reader could resolve the root before its children exist remotely."
  mutant := mutantStep

end Effects.Mutants.RMT007PublishUnconfirmed
