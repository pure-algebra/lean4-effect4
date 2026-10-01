import Effects.Algebra.Universal

/-!
# P1 — the signature sum is the coproduct of the free monads

Formal pass, seat ALGEBRA, 2026-10-01. Question: the pinned package proves the free monad's
universal property (`program_is_free`, `program_is_initial_in_models_eq`) and the injection
laws (`inl_bind`, `inl_injective`, `interpret_inl`), but states no theorem that
`Program (S ⊕ₛ T)` is the coproduct of `Program S` and `Program T` in the category of monads and
monad morphisms (Hyland, Plotkin, Power 2006: the sum of free theories), nor the restriction law
for an arbitrary handler of a sum. Both hold; this file proves them from the package's own
lemmas, and pins with a red control that the sum carries no tensor (commutation) equation.
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P1

open Effects

universe uS uT uAns v

variable {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}

section Restriction

variable {M : Type uAns → Type v}

/-- A handler of the sum, restricted along the left injection. -/
def restrictL (h : Handler (Signature.sum S T) M) : Handler S M :=
  ⟨fun op => h.handle (.inl op)⟩

/-- A handler of the sum, restricted along the right injection. -/
def restrictR (h : Handler (Signature.sum S T) M) : Handler T M :=
  ⟨fun op => h.handle (.inr op)⟩

/-- Every handler of a sum is the copairing of its two restrictions. -/
theorem eq_sum_restrict (h : Handler (Signature.sum S T) M) :
    h = (restrictL h).sum (restrictR h) :=
  Handler.sum_unique _ _ h (fun _ => rfl) (fun _ => rfl)

variable [Monad M]

/-- **The restriction law.** Interpreting an injected program under any handler of the sum is
interpreting it under the handler's restriction (no monad law is used). -/
theorem interpret_inl_restrict (h : Handler (Signature.sum S T) M) {A : Type uAns}
    (p : Program S A) : interpret h (Program.inl p) = interpret (restrictL h) p := by
  have e := interpret_inl (restrictL h) (restrictR h) p
  rw [← eq_sum_restrict h] at e
  exact e

theorem interpret_inr_restrict (h : Handler (Signature.sum S T) M) {A : Type uAns}
    (p : Program T A) : interpret h (Program.inr p) = interpret (restrictR h) p := by
  have e := interpret_inr (restrictL h) (restrictR h) p
  rw [← eq_sum_restrict h] at e
  exact e

end Restriction

section Coproduct

/-- The injections are monad morphisms into the free monad of the sum. -/
theorem inl_isMonadMorphism :
    IsMonadMorphism S (M := Program (Signature.sum S T)) (fun p => Program.inl p) where
  pure_law _ := rfl
  bind_law p k := Program.inl_bind p k

theorem inr_isMonadMorphism :
    IsMonadMorphism T (M := Program (Signature.sum S T)) (fun p => Program.inr p) where
  pure_law _ := rfl
  bind_law p k := Program.inr_bind p k

variable {M : Type uAns → Type v} [Monad M]

/-- The copairing of two maps out of the free monads: interpret by the summed handler their
operation clauses induce. -/
def copair (f : {A : Type uAns} → Program S A → M A) (g : {A : Type uAns} → Program T A → M A) :
    {A : Type uAns} → Program (Signature.sum S T) A → M A :=
  fun p => interpret (Handler.sum ⟨fun op => f (Program.perform op)⟩
    ⟨fun op => g (Program.perform op)⟩) p

/-- **The sum of free theories is the coproduct of the free monads.** For monad morphisms
`f : Program S → M` and `g : Program T → M` into a lawful monad there is exactly one monad
morphism out of `Program (S ⊕ₛ T)` that restricts to `f` along `inl` and to `g` along `inr`. -/
theorem sum_is_coproduct [LawfulMonad M]
    (f : {A : Type uAns} → Program S A → M A) (g : {A : Type uAns} → Program T A → M A)
    (hf : IsMonadMorphism S f) (hg : IsMonadMorphism T g) :
    IsMonadMorphism (Signature.sum S T) (copair f g) ∧
      (∀ {A : Type uAns} (p : Program S A), copair f g (Program.inl p) = f p) ∧
      (∀ {A : Type uAns} (p : Program T A), copair f g (Program.inr p) = g p) ∧
      ∀ h : {A : Type uAns} → Program (Signature.sum S T) A → M A,
        IsMonadMorphism (Signature.sum S T) h →
        (∀ {A : Type uAns} (p : Program S A), h (Program.inl p) = f p) →
        (∀ {A : Type uAns} (p : Program T A), h (Program.inr p) = g p) →
        ∀ {A : Type uAns} (p : Program (Signature.sum S T) A), h p = copair f g p := by
  refine ⟨interpret_isMonadMorphism _, ?_, ?_, ?_⟩
  · intro A p
    show interpret _ (Program.inl p) = f p
    rw [interpret_inl]
    exact (interpret_of_isMonadMorphism f hf p).symm
  · intro A p
    show interpret _ (Program.inr p) = g p
    rw [interpret_inr]
    exact (interpret_of_isMonadMorphism g hg p).symm
  · intro h hh hl hr A p
    rw [interpret_of_isMonadMorphism h hh p]
    show interpret _ p = interpret _ p
    congr 1
    apply Handler.sum_unique
    · intro op
      exact hl (Program.perform op)
    · intro op
      exact hr (Program.perform op)

end Coproduct

/-! ## Red control: the sum is not a tensor

In Hyland–Plotkin–Power's terms the tensor adds the equations that every operation of one theory
commutes with every operation of the other. The free sum has none: a left operation followed by
a right one is a different tree from the right one followed by the left one. The tree's
`RSig = StoreSig ⊕ₛ FiberSig` is such a sum, so nothing may assume that a store operation
commutes with a fiber operation. -/

theorem sum_not_tensor (s : S.Op) (t : T.Op) {A : Type uAns}
    (k₁ : S.Answer s → Program (Signature.sum S T) A)
    (k₂ : T.Answer t → Program (Signature.sum S T) A) :
    Program.vis (signature := Signature.sum S T) (.inl s) k₁ ≠
      Program.vis (signature := Signature.sum S T) (.inr t) k₂ := by
  intro h
  injection h with hop
  cases hop

end FormalPass.Algebra.P1

#print axioms FormalPass.Algebra.P1.interpret_inl_restrict
#print axioms FormalPass.Algebra.P1.interpret_inr_restrict
#print axioms FormalPass.Algebra.P1.inl_isMonadMorphism
#print axioms FormalPass.Algebra.P1.sum_is_coproduct
#print axioms FormalPass.Algebra.P1.sum_not_tensor
#print axioms FormalPass.Algebra.P1.eq_sum_restrict
#print axioms FormalPass.Algebra.P1.inr_isMonadMorphism
