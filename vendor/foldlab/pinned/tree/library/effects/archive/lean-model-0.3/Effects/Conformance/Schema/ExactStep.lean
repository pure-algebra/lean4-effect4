import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA EXACT-STEP. Sentence template: "When <hypothesis>, one reducer
step changes <measure> by exactly <delta> — <domain gloss>." Kit template: a
well-formed positive case satisfying the hypothesis, and a case where the
hypothesis fails, proving the hypothesis discriminates. -/
structure ExactStep (State Input : Type) where
  id : String
  sentence : String
  wf : State → Prop
  hyp : State → Input → Prop
  step : State → Input → State
  measure : State → Nat
  delta : Nat
  law : ∀ s i, wf s → hyp s i → measure (step s i) = measure s + delta
  posState : State
  posInput : Input
  pos_wf : wf posState
  pos_hyp : hyp posState posInput
  negState : State
  negInput : Input
  neg_hyp : ¬ hyp negState negInput

def ExactStep.entry {State Input : Type} (b : ExactStep State Input) : LedgerEntry :=
  { id := b.id, family := "EXACT-STEP", sentence := b.sentence }

end Effects.Conformance
