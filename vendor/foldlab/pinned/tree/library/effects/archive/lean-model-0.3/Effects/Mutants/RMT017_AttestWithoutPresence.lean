import Effects.Conformance.ManifestRemote
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RMT017AttestWithoutPresence

open Effects.Remote Effects.Conformance Effects.Conformance.Manifest

/-- A machine that confirms any locally verified attestation, presence
report or not — a peer that never claimed the key gets it published
against them anyway. -/
def mutantStep : RStep := fun s i =>
  match i with
  | .request id (.attest key bytes) =>
    if vecParams.verify key bytes then
      { result := .attested key
        state := { s with confirmed := s.confirmed.insert key }
        commands := []
        decisions := [(id, .confirmedByAttestation key)] }
    else Effects.Remote.step vecParams s i
  | _ => Effects.Remote.step vecParams s i

def mutant : Mutant RStep where
  id := "RMT017_AttestWithoutPresence"
  attacks := "RMT-017"
  represents := "Killing this mutant demonstrates the vectors notice a machine that confirms an attestation the peer never solicited with a presence report — local bytes alone must never entitle a publication claim about the peer."
  mutant := mutantStep

end Effects.Mutants.RMT017AttestWithoutPresence
