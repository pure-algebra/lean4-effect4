/-!
# Sentence riders

A ratified sentence sometimes claims more than its schema bundle's law
fields force: a conjunct discharged by a named model theorem that the
instance only cites in prose. A rider makes that citation load-bearing —
the statement and its proof are fields, so renaming, weakening, or
deleting the theorem breaks this declaration at build time, never just a
docstring. Sentences never narrow; the rider is how the extra conjunct
stays proved. Riders are declared beside their instances and collected,
coverage-checked, in the registry.
-/

namespace Effects.Conformance

structure SentenceRider where
  /-- The obligation whose ratified sentence carries the conjunct. -/
  id : String
  /-- The sentence fragment the theorem discharges, quoted. -/
  conjunct : String
  prop : Prop
  proof : prop

/-- Rider constructor inferring the statement from the proof term, so
the discharging theorem is named exactly once. Reference theorems in
`@`-form: the fully quantified constant is itself the proposition. -/
def SentenceRider.of (id conjunct : String) {P : Prop} (proof : P) :
    SentenceRider := ⟨id, conjunct, P, proof⟩

end Effects.Conformance
