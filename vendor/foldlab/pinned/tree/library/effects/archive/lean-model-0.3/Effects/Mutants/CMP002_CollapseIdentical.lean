import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.CMP002CollapseIdentical

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- Content-keyed occurrence reuse: an append whose entry equals the last
recorded entry is silently dropped — the named defect. -/
def mutantReduce : RReducer := fun s i =>
  match i with
  | .recorded inv out =>
    if s.history.getLast? = some (inv.entry out) then
      { result := .appended, state := s
        decisions := [.occurrenceAppended inv.op (s.cursor - 1)] }
    else reduce s i
  | _ => reduce s i

def mutant : Mutant RReducer where
  id := "CMP002_CollapseIdentical"
  attacks := "CMP-002"
  represents := "Killing this mutant demonstrates the vectors notice identical invocation content collapsing into one occurrence — request-content-keyed reuse answering an occurrence."
  mutant := mutantReduce

end Effects.Mutants.CMP002CollapseIdentical
