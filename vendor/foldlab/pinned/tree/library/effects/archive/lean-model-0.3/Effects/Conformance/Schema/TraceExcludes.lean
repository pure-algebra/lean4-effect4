import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA TRACE-EXCLUDES. Sentence template: "In <guarded mode>, no step
ever emits <excluded decision> — <domain gloss>." Kit template: a positive
case inside the guarded mode, and a case outside the guarded mode where the
excluded decision does occur, proving the mode guard is not vacuous. -/
structure TraceExcludes (State Input Decision Mode : Type) where
  id : String
  sentence : String
  modeOf : State → Mode
  guarded : Mode
  decisions : State → Input → List Decision
  bad : Decision
  law : ∀ s i, modeOf s = guarded → bad ∉ decisions s i
  posState : State
  posInput : Input
  pos_mode : modeOf posState = guarded
  negState : State
  negInput : Input
  neg_mode : modeOf negState ≠ guarded
  neg_bad : bad ∈ decisions negState negInput

def TraceExcludes.entry {State Input Decision Mode : Type}
    (b : TraceExcludes State Input Decision Mode) : LedgerEntry :=
  { id := b.id, family := "TRACE-EXCLUDES", sentence := b.sentence }

end Effects.Conformance
