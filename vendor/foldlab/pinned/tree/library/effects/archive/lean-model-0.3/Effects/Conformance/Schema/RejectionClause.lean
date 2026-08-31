import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA REJECTION-CLAUSE. Sentence template: "Admission rejects exactly
the raw values a named clause condemns, and every rejection names its
clause — <domain gloss>." Kit template: a raw value that admits, and a raw
value rejected with its named clause. -/
structure RejectionClause (Raw Admitted Clause : Type) where
  id : String
  sentence : String
  admit : Raw → Except Clause Admitted
  clauseProp : Clause → Raw → Prop
  law_sound : ∀ r c, admit r = Except.error c → clauseProp c r
  law_complete : ∀ r, (∃ c, clauseProp c r) → ∃ c', admit r = Except.error c'
  posRaw : Raw
  pos_admits : ∃ a, admit posRaw = Except.ok a
  negRaw : Raw
  negClause : Clause
  neg_rejects : admit negRaw = Except.error negClause

def RejectionClause.entry {Raw Admitted Clause : Type}
    (b : RejectionClause Raw Admitted Clause) : LedgerEntry :=
  { id := b.id, family := "REJECTION-CLAUSE", sentence := b.sentence }

end Effects.Conformance
