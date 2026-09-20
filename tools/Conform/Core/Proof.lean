import ProofGraph.Proof

/-! Compatibility names for Conform's consumers. Checked evidence is owned by the
shared proof graph so Laws and conformance tools use the same validator. -/
namespace Conform
abbrev ProofRef := ProofGraph.ProofRef
namespace ProofRef
abbrev mk := ProofGraph.ProofRef.mk
def validate (p : ProofRef) : Lean.MetaM (Except String Unit) := ProofGraph.ProofRef.validate p
end ProofRef
end Conform
