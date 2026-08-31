import Effects.Conformance.Ledger

namespace Effects.Conformance

/-- SCHEMA AGREEMENT (added at the remote Pass A; generalized to the
relational form at the R1 correction — the operator's review required
refinement across different result types and trace-inclusive
observations to be expressible). Sentence template: "On <domain>,
<computation A> and <computation B> agree at <observation> under
<relation> — <domain gloss>." Equality instances set the relation to
`Eq` over a common observation type. Kit template: a positive witness
where the related observation holds, and a falsification witness — a
mutated computation that satisfies the hypothesis yet observably
diverges. Observations must be frozen per instance and include emitted
commands wherever a silent side effect could fake agreement. -/
structure Agreement (X R S O₁ O₂ : Type) where
  id : String
  sentence : String
  hyp : X → Prop
  observeF : R → O₁
  observeG : S → O₂
  rel : O₁ → O₂ → Prop
  f : X → R
  g : X → S
  law : ∀ x, hyp x → rel (observeF (f x)) (observeG (g x))
  posX : X
  pos_hyp : hyp posX
  negF : X → R
  negX : X
  neg_hyp : hyp negX
  neg_diverges : ¬ rel (observeF (negF negX)) (observeG (g negX))

def Agreement.entry {X R S O₁ O₂ : Type}
    (b : Agreement X R S O₁ O₂) : LedgerEntry :=
  { id := b.id, family := "AGREEMENT", sentence := b.sentence }

end Effects.Conformance
