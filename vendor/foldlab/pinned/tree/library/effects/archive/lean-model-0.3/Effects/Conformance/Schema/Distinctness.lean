import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA DISTINCTNESS. Sentence template: "Two occurrences with identical
<content> remain distinct <identities> — <domain gloss>." Kit template:
positive-only by shape — an exhibited content-equal pair; denying the law
itself would be the only falsification, so no negative witness field
exists. -/
structure Distinctness (State Input OccId Content : Type) where
  id : String
  sentence : String
  contentOf : Input → Content
  emit : State → Input → OccId × State
  law : ∀ s i i', contentOf i = contentOf i' →
    (emit s i).1 ≠ (emit (emit s i).2 i').1
  posState : State
  posInput : Input
  posInput' : Input
  pos_content : contentOf posInput = contentOf posInput'

def Distinctness.entry {State Input OccId Content : Type}
    (b : Distinctness State Input OccId Content) : LedgerEntry :=
  { id := b.id, family := "DISTINCTNESS", sentence := b.sentence }

end Effects.Conformance
