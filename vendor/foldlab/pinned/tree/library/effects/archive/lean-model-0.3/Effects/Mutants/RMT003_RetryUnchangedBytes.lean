import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT003RetryUnchangedBytes

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A client that re-issues an upload for content already
integrity-rejected — the terminal-integrity memory ignored. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .request id (.upload key bytes) =>
    match s.inFlight[id]? with
    | none =>
      if s.rejected.contains (key, bytes) then
        { result := .commanded
          state := { s with inFlight := s.inFlight.insert id (.uploading key bytes) }
          commands := [(id, .upload key bytes)]
          decisions := [(id, .issued (.upload key bytes))] }
      else Effects.Remote.step vecParams s i
    | some _ => Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT003_RetryUnchangedBytes"
  attacks := "RMT-003"
  represents := "Killing this mutant demonstrates the vectors notice a client that retries an upload with unchanged, already-rejected content — an integrity failure must be terminal for those bytes."
  mutant := mutantStep

end Effects.Mutants.RMT003RetryUnchangedBytes
