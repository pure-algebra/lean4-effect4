import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA WF-PRESERVE. Sentence template: "When <hypothesis>, one step from
a well-formed <state> yields a well-formed <state> — <domain gloss>."
Kit template: a well-formed positive case satisfying the hypothesis, and an
ill-formed raw state as the falsification witness. -/
structure WfPreserve (State Input : Type) where
  id : String
  sentence : String
  wf : State → Prop
  hyp : State → Input → Prop
  step : State → Input → State
  law : ∀ s i, wf s → hyp s i → wf (step s i)
  posState : State
  posInput : Input
  pos_wf : wf posState
  pos_hyp : hyp posState posInput
  negState : State
  neg_ill : ¬ wf negState

def WfPreserve.entry {State Input : Type} (b : WfPreserve State Input) : LedgerEntry :=
  { id := b.id, family := "WF-PRESERVE", sentence := b.sentence }

end Effects.Conformance
