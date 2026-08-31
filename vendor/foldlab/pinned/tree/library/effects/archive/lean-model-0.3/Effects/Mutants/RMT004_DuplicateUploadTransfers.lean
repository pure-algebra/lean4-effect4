import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT004DuplicateUploadTransfers

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that re-transfers content already admitted for its key —
the dedup branch ignored, duplicate wire traffic issued anyway. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .request id (.upload key bytes) =>
    match s.inFlight[id]? with
    | none =>
      if vecParams.size bytes > vecParams.budgets.maxBytes then
        Effects.Remote.step vecParams s i
      else if s.rejected.contains (key, bytes) then
        Effects.Remote.step vecParams s i
      else if vecParams.verify key bytes then
        if s.cache.contains key then
          { result := .commanded
            state := { s with
                       inFlight := s.inFlight.insert id (.uploading key bytes) }
            commands := [(id, .upload key bytes)]
            decisions := [(id, .verified key), (id, .issued (.upload key bytes))] }
        else Effects.Remote.step vecParams s i
      else Effects.Remote.step vecParams s i
    | some _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT004_DuplicateUploadTransfers"
  attacks := "RMT-004"
  represents := "Killing this mutant demonstrates the vectors notice a client that re-transfers content already admitted for its key — an already-present exact-digest upload must resolve as success with zero additional transfer commands."
  mutant := mutantStep

end Effects.Mutants.RMT004DuplicateUploadTransfers
