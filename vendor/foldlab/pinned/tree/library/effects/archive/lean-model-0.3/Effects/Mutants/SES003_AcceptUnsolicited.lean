import Effects.Conformance.ManifestReplay
import Effects.Conformance.Mutant

/-!
Declared mutant. Quarantined: the model never imports this tree.
-/

namespace Effects.Mutants.SES003AcceptUnsolicited

open Effects.Replay Effects.Conformance Effects.Conformance.Manifest

/-- A reducer that appends every record-mode outcome unconditionally,
solicited or not — the pre-protocol behavior through which a cross-wired
or duplicated outcome silently enters a durable history. -/
def mutantReduce : RReducer := fun s i =>
  match s.status, s.mode, i with
  | .active, .record, .recorded inv out =>
    { result := .appended
      state := { s with
                 pending := none,
                 history := s.history ++ [inv.entry out],
                 cursor := s.cursor + 1 }
      decisions := [.occurrenceAppended inv.op s.cursor] }
  | _, _, _ => reduce s i

def mutant : Mutant RReducer where
  id := "SES003_AcceptUnsolicited"
  attacks := "SES-003"
  represents := "Killing this mutant demonstrates the vectors notice a reducer that appends an outcome nobody solicited — without the solicitation refusal, a cross-wired or duplicated outcome enters a durable history silently."
  mutant := mutantReduce

end Effects.Mutants.SES003AcceptUnsolicited
