import Effect4.Program.Provision
import Effect4.Laws.Program.TypeAlgebra

/-!
# Laws.Program.Provision — the provision algebra on the whole layer type

`Program/Provision.lean` is in the core root and states the provision algebra's associativity
laws on the rows (`provide_provide_rows`, `provideMerge_assoc_rows`), because the error column
is `Ty.join`, whose associativity (`Ty.join_assoc`, `Laws/Program/TypeAlgebra.lean`) is a law of
the proof graph. This module, in the proof graph, states them on the whole layer type (formal
pass, algebra verification ALG-16, `algebra/verify-ProvideMerge.lean`):

* `provideMerge_assoc`: `provideMerge` is associative;
* `provide_provide`: providing two dependencies one after the other is providing their
  `provideMerge` at once, error column included.

Plain associativity of `provide` fails already on the rows (`provide_not_assoc`,
`Test/Program/ProvideRows.lean`), so a printer step or a form may regroup a `provideMerge`
chain, never a `provide` chain.
-/

set_option autoImplicit false

namespace Effect4.Program.Provision

namespace LayerTy

open Effect4 Effect4.Program

/-- **`provideMerge` is associative**, on the whole layer type: the rows by
`provideMerge_assoc_rows`, the error column by `Ty.join_assoc`. -/
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

/-- **Provide is associative up to `provideMerge`**, on the whole layer type: the rows by
`provide_provide_rows`, the error column by `Ty.join_assoc`. -/
theorem provide_provide (l d₁ d₂ : LayerTy) :
    (l.provide d₁).provide d₂ = l.provide (d₁.provideMerge d₂) := by
  obtain ⟨hout, hreq⟩ := provide_provide_rows l d₁ d₂
  have herr : ((l.provide d₁).provide d₂).error = (l.provide (d₁.provideMerge d₂)).error :=
    Ty.join_assoc _ _ _
  cases hl : (l.provide d₁).provide d₂
  cases hr : l.provide (d₁.provideMerge d₂)
  rw [hl, hr] at hout hreq herr
  simp only at hout hreq herr
  rw [hout, hreq, herr]

end LayerTy

end Effect4.Program.Provision
