import Effect4.Laws.Program.Provision

/-!
# `provide` on requirement rows: associative only up to `provideMerge`

Controls for the provision algebra's associativity laws (`Program/Provision.lean`:
`provide_provide_rows`, `provideMerge_assoc_rows`; `Laws/Program/Provision.lean`:
`provide_provide`, `provideMerge_assoc`). Red (formal pass, algebra note §2.8, probe
`P7ProvideRows.lean`): plain associativity of `provide` fails on the rows, because a nested
`provide` hides the inner dependency's outputs from the outer dependent (rc.112's
`Layer.provide` keeps only the dependent's outputs, `Program/Typing/Rules.lean`'s `provide`).
Positive: on the same three layers the `provideMerge` grouping is free, error column included.
-/

set_option autoImplicit false
namespace Test.Program.ProvideRows
open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)

/-- One service key. -/
def a : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩

/-- A dependent that needs `a`; a dependency that provides nothing; a dependency that provides
`a`. -/
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

/-- The `provideMerge` grouping of the same layers is free, error column included. -/
theorem provideMerge_regroups :
    (l.provideMerge d₁).provideMerge d₂ = l.provideMerge (d₁.provideMerge d₂) :=
  Provision.LayerTy.provideMerge_assoc l d₁ d₂

/-- And the sequenced `provide` is the `provideMerge` of the dependencies, error column
included. -/
theorem provide_sequenced : (l.provide d₁).provide d₂ = l.provide (d₁.provideMerge d₂) :=
  Provision.LayerTy.provide_provide l d₁ d₂

/-! Plain associativity is refused by evaluation as well. -/

/--
error: Tactic `decide` proved that the proposition
  ((l.provide d₁).provide d₂).requires = (l.provide (d₁.provide d₂)).requires
is false
-/
#guard_msgs (error) in
example : ((l.provide d₁).provide d₂).requires = (l.provide (d₁.provide d₂)).requires := by
  decide

#print axioms provide_not_assoc
#print axioms provideMerge_regroups
#print axioms provide_sequenced
end Test.Program.ProvideRows
