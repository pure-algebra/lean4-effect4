import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.RPL005AcceptSuffix

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- Completion that ignores an unconsumed suffix and reports success. -/
def mutantReduce : RReducer := fun s i =>
  match i with
  | .complete t =>
    let o := reduce s i
    match o.result with
    | .outcome (.rejected .unconsumedSuffix _ _) =>
        { result := .outcome (.completed t), state := s
          decisions := [.completed s.cursor] }
    | _ => o
  | _ => reduce s i

def mutant : Mutant RReducer where
  id := "RPL005_AcceptSuffix"
  attacks := "RPL-005"
  represents := "Killing this mutant demonstrates the vectors notice a completion that hides recorded actions never re-emitted — the same final value must not mask an unconsumed suffix."
  mutant := mutantReduce

end Effects.Mutants.RPL005AcceptSuffix
