import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.SES003AcceptInterleavedInvoke

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- A reducer that delegates every record-mode invocation regardless of
an outstanding delegation, silently overwriting the registration — the
pre-protocol behavior whose histories order by completion. -/
def mutantReduce : RReducer := fun s i =>
  match s.status, s.mode, i with
  | .active, .record, .invoke inv =>
    { result := .delegated
      state := { s with pending := some inv }
      decisions := [.liveDelegation inv.op s.cursor] }
  | _, _, _ => reduce s i

def mutant : Mutant RReducer where
  id := "SES003_AcceptInterleavedInvoke"
  attacks := "SES-003"
  represents := "Killing this mutant demonstrates the vectors notice a reducer that accepts a second invocation while a delegation is outstanding — the exclusivity refusal, not scheduling luck, is what keeps histories in invocation order."
  mutant := mutantReduce

end Effects.Mutants.SES003AcceptInterleavedInvoke
