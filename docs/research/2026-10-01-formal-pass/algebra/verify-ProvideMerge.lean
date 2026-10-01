import Effect4.Program.Provision
import Effect4.Laws.Program.TypeAlgebra

/-!
# verify-ProvideMerge — ALG-16's "provideMerge chains regroup freely", checked

Adversarial verifier of seat ALGEBRA, formal pass, 2026-10-01. ALG-16 recommends recording that
"a printer step or form may regroup `provideMerge` chains freely but not `provide` chains". The
tree proves `provide_provide_rows` (`Program/Provision.lean:123`) on the rows only, because its
docstring says `Ty.join`'s associativity "is an owed row of the type language"; no `provideMerge`
associativity is stated. `Ty.join_assoc` is proved (`Laws/Program/TypeAlgebra.lean:433`), so the
docstring is stale. Proved here:

* `provideMerge_assoc_rows`: `provideMerge` is associative on the rows;
* `provideMerge_assoc`: and on the whole layer type, error column included;
* `provide_provide`: the tree's row law upgraded to the whole layer type.
-/

set_option autoImplicit false

namespace FormalPass.AlgebraVerify.ProvideMerge

open Effect4 Effect4.Program

theorem provideMerge_assoc_rows (l d₁ d₂ : LayerTy) :
    ((l.provideMerge d₁).provideMerge d₂).out = (l.provideMerge (d₁.provideMerge d₂)).out ∧
      ((l.provideMerge d₁).provideMerge d₂).requires =
        (l.provideMerge (d₁.provideMerge d₂)).requires := by
  refine ⟨Row.union_assoc _ _ _, ?_⟩
  apply Row.eq_of_mem_iff
  intro a
  simp only [LayerTy.provideMerge, Row.mem_union, Row.mem_diff, not_or]
  by_cases hL : a ∈ l.requires <;> by_cases hO₁ : a ∈ d₁.out <;> by_cases hO₂ : a ∈ d₂.out <;>
    by_cases hR₁ : a ∈ d₁.requires <;> by_cases hR₂ : a ∈ d₂.requires <;>
    simp only [hL, hO₁, hO₂, hR₁, hR₂, and_true, not_true, not_false_eq_true, and_false,
      or_true, or_false]

theorem provideMerge_assoc (l d₁ d₂ : LayerTy) :
    (l.provideMerge d₁).provideMerge d₂ = l.provideMerge (d₁.provideMerge d₂) := by
  obtain ⟨hout, hreq⟩ := provideMerge_assoc_rows l d₁ d₂
  have herr : ((l.provideMerge d₁).provideMerge d₂).error =
      (l.provideMerge (d₁.provideMerge d₂)).error := Ty.join_assoc _ _ _
  cases hl : (l.provideMerge d₁).provideMerge d₂
  cases hr : l.provideMerge (d₁.provideMerge d₂)
  rw [hl, hr] at hout hreq herr
  simp only at hout hreq herr
  rw [hout, hreq, herr]

theorem provide_provide (l d₁ d₂ : LayerTy) :
    (l.provide d₁).provide d₂ = l.provide (d₁.provideMerge d₂) := by
  obtain ⟨hout, hreq⟩ := Provision.LayerTy.provide_provide_rows l d₁ d₂
  have herr : ((l.provide d₁).provide d₂).error = (l.provide (d₁.provideMerge d₂)).error :=
    Ty.join_assoc _ _ _
  cases hl : (l.provide d₁).provide d₂
  cases hr : l.provide (d₁.provideMerge d₂)
  rw [hl, hr] at hout hreq herr
  simp only at hout hreq herr
  rw [hout, hreq, herr]

end FormalPass.AlgebraVerify.ProvideMerge

#print axioms FormalPass.AlgebraVerify.ProvideMerge.provideMerge_assoc_rows
#print axioms FormalPass.AlgebraVerify.ProvideMerge.provideMerge_assoc
#print axioms FormalPass.AlgebraVerify.ProvideMerge.provide_provide
