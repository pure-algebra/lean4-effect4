import Effects.Conformance.Schema.RejectionClause
import Effects.Cas.Admission

/-!
# CAS-002 — the node-admission rejection instance

The REJECTION-CLAUSE schema bundle over store admission. The raw values are
nodes checked against a fixed kit store; the clauses are the clause-named
admission errors, characterized by what each condemns; soundness and
completeness are the landed checker theorems. The kit store binds one
resident node, the admitting node references it at its declared kind, and
the rejected node references an unbound address — rejected as dangling.
-/

namespace Effects.Conformance

open Effects.Cas

/-- The kit store's one bound address: thirty-two zero bytes. -/
def cas002Bound : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- An address the kit store never binds: thirty-two one bytes. -/
def cas002Missing : Addr32 := ⟨List.replicate 32 1, by simp⟩

/-- The kit store's one resident: a node of kind tag five. -/
def cas002Resident : Node := ⟨0, 5, [], []⟩

/-- The kit store: the resident bound at the bound address. -/
def cas002Store : Store := Store.empty.set cas002Bound cas002Resident

/-- The kit's admitting node: one typed reference to the resident, at its
declared kind. -/
def cas002Pos : Node := ⟨0, 1, [], [⟨5, cas002Bound⟩]⟩

/-- The kit's rejected node: one typed reference to the unbound address. -/
def cas002Neg : Node := ⟨0, 1, [], [⟨5, cas002Missing⟩]⟩

/-- CAS-002: admission rejects dangling or wrong-kind references. -/
def cas002 : RejectionClause Node Unit AdmissionError where
  id := "CAS-002"
  sentence := "Admission rejects exactly the raw values a named clause condemns, and every rejection names its clause — a CAS node enters the store only when every typed reference resolves at its declared kind: a reference to an unbound address is rejected as dangling, and a reference whose declared kind tag disagrees with the resident node's kind tag is rejected as wrong-kind."
  admit := fun n => admitNode cas002Store n
  clauseProp := fun c n => AdmissionError.Condemns cas002Store c n.refs
  law_sound := fun _ _ h => admitNode_error_condemns h
  law_complete := fun _ h => admitNode_complete h
  posRaw := cas002Pos
  pos_admits := ⟨(), rfl⟩
  negRaw := cas002Neg
  negClause := .dangling cas002Missing
  neg_rejects := rfl

end Effects.Conformance
