/-!
# The declared model version

Manifests bind to the declared model version, never the commit (WGR-4
rule 2): any semantics-affecting model change bumps it, regeneration under
an unchanged version must be byte-identical, and a bump is a declared
transformation that deletes the old manifests — git history keeps them
recoverable. The ratification point fires per manifest version; the
ratified list below is the committed-document record of those events, and
the ratification landing is the only edit that appends to it.
-/

namespace Effects.Conformance

/-- The declared model version every manifest binds to. 0.2.0 was the
record-mode delegation protocol (SES-003); 0.3.0 is the attested-
presence confirmation rule (RMT-017): a peer-reported-present key whose
bytes the client verifies locally confirms for publication. -/
def modelVersion : String := "effects-model@0.3.0"

/-- Manifest versions the operator has ratified. Empty means the
implementation lane has nothing to consume. Appending here is the
ratification event; each append is recorded in the workflow's
ratification record. -/
def ratifiedManifestVersions : List String :=
  ["effects-model@0.1.0", "effects-model@0.2.0", "effects-model@0.3.0"]

end Effects.Conformance
