import Effects.Conformance.Schema.FailClosed
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-002 — budgets before bytes

FAIL-CLOSED over the remote client machine: the hypothesis is "within
declared budgets", its failure — a fresh upload whose content size
exceeds the byte budget, or a load response whose declared length does
— rejects with the typed budget rejection and the cache is frozen. The
named theorems carry the exclusion form the obligation means at the
model's altitude: no verification, cache, or return decision occurs
after an over-budget declaration. The shell-side half — an oversized
declared body is never read or buffered, enforced by a streaming byte
counter — is the R2 TypeScript obligation, and the key-count budget is
R3's. The negative kit is a within-budget upload, proving rejection is
not universal.
-/

namespace Effects.Conformance

open Effects.Remote

private abbrev MSt := MachineState Nat (List UInt8)
private abbrev MIn := MInput Nat (List UInt8)
private abbrev MRes := MResult Nat (List UInt8)

/-- RMT-002: declared sizes and counts are checked against declared
budgets before any hashing or decoding. -/
def rmt002 : FailClosed MSt MIn MRes where
  id := "RMT-002"
  sentence := "When a declaration exceeds the declared budgets — a fresh upload whose content size is over the byte budget, or a load response whose declared length is — the step rejects with the typed budget rejection, the cache is unchanged, and no verification, cache, or return decision occurs: at the model's altitude nothing over budget proceeds toward admission, and the shell obligation that an oversized declared body is never read or buffered arrives with the R2 streaming byte counter."
  wf := fun _ => True
  hyp := fun s i => overBudget rmtParams s i = false
  step := fun s i =>
    ((Effects.Remote.step rmtParams s i).result,
      (Effects.Remote.step rmtParams s i).state)
  isRejection := MResult.isBudgetRejection
  measure := fun s => s.cache.size
  law_reject := fun s i _ hn =>
    RMT_002_budget_rejects rmtParams s i
      (by revert hn; cases overBudget rmtParams s i <;> simp)
  law_frozen := fun s i _ hn => by
    have hc := RMT_002_budget_frozen rmtParams s i
      (by revert hn; cases overBudget rmtParams s i <;> simp)
    simp [hc]
  posState := rmtEmpty
  posInput := .request 1 (.upload 9 (List.replicate 9 0))
  pos_wf := trivial
  pos_nohyp := by
    simp [overBudget, rmtEmpty, rmtParams]
  negState := rmtEmpty
  negInput := .request 1 (.upload 2 [7, 9])
  neg_hyp := by
    simp [overBudget, rmtEmpty, rmtParams]

end Effects.Conformance
