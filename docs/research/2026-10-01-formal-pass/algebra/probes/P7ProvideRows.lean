import Effect4.Program.Provision

/-!
# P7 — `provide` on rows: associative only up to `provideMerge`

Formal pass, seat ALGEBRA, 2026-10-01. The provision algebra proves that providing two
dependencies one after the other has the rows of providing their `provideMerge` at once
(`provide_provide_rows`, `Program/Provision.lean:123`). Red control: plain associativity of
`provide` fails on rows, because a nested `provide` hides the inner dependency's outputs from the
outer dependent (rc.112's `Layer.provide` keeps only the dependent's outputs, `Layer.ts:2258`). So
"wire the dependencies in any grouping" holds for `provideMerge`, not for `provide`, and a printer
or form that regroups `provide` chains changes the requirement row.
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P7

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

/-- One service key. -/
def a : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩

/-- A dependent that needs `a`; a dependency that provides nothing; a dependency that provides `a`. -/
def l : LayerTy := ⟨Requirement.empty, .never, Requirement.single a⟩
def d₁ : LayerTy := ⟨Requirement.empty, .never, Requirement.empty⟩
def d₂ : LayerTy := ⟨Requirement.single a, .never, Requirement.empty⟩

theorem a_needed_nested : a ∈ (l.provide (d₁.provide d₂)).requires := by
  show a ∈ Row.union (Row.diff (Requirement.single a) Requirement.empty)
    (Row.union (Row.diff Requirement.empty (Requirement.single a)) Requirement.empty)
  rw [Row.mem_union, Row.mem_diff]
  exact Or.inl ⟨(Row.mem_singleton a a).mpr rfl, Row.not_mem_empty a⟩

theorem a_discharged_sequenced : a ∉ ((l.provide d₁).provide d₂).requires := by
  show a ∉ Row.union (Row.diff (Row.union (Row.diff (Requirement.single a) Requirement.empty)
    Requirement.empty) (Requirement.single a)) Requirement.empty
  rw [Row.mem_union, Row.mem_diff]
  intro h
  rcases h with ⟨_, hout⟩ | hempty
  · exact hout ((Row.mem_singleton a a).mpr rfl)
  · exact Row.not_mem_empty a hempty

/-- **Red control: `provide` is not associative on requirement rows.** -/
theorem provide_not_assoc :
    ((l.provide d₁).provide d₂).requires ≠ (l.provide (d₁.provide d₂)).requires := by
  intro h
  exact a_discharged_sequenced (h ▸ a_needed_nested)

end FormalPass.Algebra.P7

#print axioms FormalPass.Algebra.P7.provide_not_assoc
#print axioms FormalPass.Algebra.P7.a_needed_nested
#print axioms FormalPass.Algebra.P7.a_discharged_sequenced
