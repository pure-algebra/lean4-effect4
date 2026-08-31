import Effects.Conformance.ManifestServer
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.SRV001AdmitDangling

open Effects.Cas Effects.Server Effects.Conformance
open Effects.Conformance.Manifest

/-- A judgment that never consults the declared references — a server
admitting a parent whose children it does not hold. -/
def mutantJudge : SrvJudgeFn := fun bytes _residents resident =>
  match decodeAdmitted bytes with
  | none => .refused
  | some _ =>
    match resident with
    | some residentBytes =>
      if residentBytes = bytes then .alreadyResident else .refused
    | none => .admit

def mutant : Mutant SrvJudgeFn where
  id := "SRV001_AdmitDangling"
  attacks := "SRV-001"
  represents := "Killing this mutant demonstrates the session vectors notice a server that admits a node without holding its declared references — the dangling upload must refuse, and the transcript must show the reference loads that justify every admission."
  mutant := mutantJudge

end Effects.Mutants.SRV001AdmitDangling
