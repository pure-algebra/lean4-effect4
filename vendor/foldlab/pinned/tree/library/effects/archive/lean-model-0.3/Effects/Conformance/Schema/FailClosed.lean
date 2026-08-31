import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA FAIL-CLOSED. Sentence template: "When <hypothesis> fails, the
step rejects with a typed result and <measure> is unchanged — <domain
gloss>." Kit template: a well-formed case where the hypothesis fails and
rejection fires, and a case where the hypothesis holds, proving rejection is
not universal. -/
structure FailClosed (State Input Result : Type) where
  id : String
  sentence : String
  wf : State → Prop
  hyp : State → Input → Prop
  step : State → Input → Result × State
  isRejection : Result → Bool
  measure : State → Nat
  law_reject : ∀ s i, wf s → ¬ hyp s i → isRejection (step s i).1 = true
  law_frozen : ∀ s i, wf s → ¬ hyp s i → measure (step s i).2 = measure s
  posState : State
  posInput : Input
  pos_wf : wf posState
  pos_nohyp : ¬ hyp posState posInput
  negState : State
  negInput : Input
  neg_hyp : hyp negState negInput

def FailClosed.entry {State Input Result : Type}
    (b : FailClosed State Input Result) : LedgerEntry :=
  { id := b.id, family := "FAIL-CLOSED", sentence := b.sentence }

end Effects.Conformance
