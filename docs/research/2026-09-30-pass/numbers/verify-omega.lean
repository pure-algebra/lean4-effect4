/-! # Verifier probe: `omega` on an `↔` goal and the axiom ceiling

Research evidence written by the adversarial verifier for the numbers seat, outside the Test
root. The first draft of `verify-edges.lean` closed two `↔` goals with a bare `omega` and its
`#print axioms` showed `Classical.choice`. This file isolates that: the same fact, once with
`omega` on the `↔` goal and once with the `↔` split first. Nothing is imported. -/

set_option autoImplicit false

namespace Research.Pass.Numbers.VerifyOmega

/-- `omega` on the whole `↔`. -/
theorem iff_by_omega (a b B : Nat) : (a + b ≤ B ∧ 0 ≤ B) ↔ a + b ≤ B := by
  omega

/-- The same fact, the `↔` split by hand, `omega` only on atomic goals. -/
theorem iff_split (a b B : Nat) : (a + b ≤ B ∧ 0 ≤ B) ↔ a + b ≤ B := by
  constructor
  · intro h
    obtain ⟨h1, _⟩ := h
    omega
  · intro h
    exact ⟨by omega, by omega⟩

/-- `omega` on one atomic goal with a conjunction hypothesis. -/
theorem atomic_by_omega (a b B : Nat) (h : a + b ≤ B ∧ 0 ≤ B) : a ≤ B := by
  omega

#print axioms iff_by_omega
#print axioms iff_split
#print axioms atomic_by_omega

end Research.Pass.Numbers.VerifyOmega
