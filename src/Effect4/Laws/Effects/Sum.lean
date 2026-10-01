import Effects.Algebra.Universal

/-!
# Laws.Effects.Sum — the signature sum is the coproduct of the free monads

Formal pass, algebra note A6 (`docs/research/2026-10-01-formal-pass/algebra/note.md` §2.1; probe
`algebra/probes/P1Coproduct.lean`, confirmed by its verifier as ALG-06). The pinned package
proves the free monad's universal property (`program_is_free`, `program_is_initial_in_models_eq`),
the sum handler's uniqueness (`Handler.sum_unique`) and the injection laws (`interpret_inl`,
`Program.inl_bind`, `Program.inl_injective`), but no theorem says that `Program (S ⊕ₛ T)` is the
coproduct of `Program S` and `Program T` among monads and monad morphisms, the sum of free
theories (Hyland, Plotkin and Power 2006, by name). This module states it (`sum_is_coproduct`),
with the restriction law for an arbitrary handler of a sum (`interpret_inl_restrict`,
`interpret_inr_restrict`, which use no monad law) and the injections as monad morphisms
(`inl_isMonadMorphism`, `inr_isMonadMorphism`).

The sum carries no commutation equations: a left operation followed by a right one is a
different tree from the reverse (the red control `sum_not_tensor`,
`Test/Program/SignatureSum.lean`). So the tree's `RSig = StoreSig ⊕ₛ FiberSig` is a sum, not a
tensor, and nothing may assume that a store operation commutes with a fiber operation (fiber
operations read and write the stores). The sums here are of free theories, hence conservative
(`Program.inl_injective`, and `Typed.inl_iff` for typing); a sum of theories with equations is
Hyland, Plotkin and Power's question, not this module's.

The module sits beside the protocol layer and not in the pinned `Effects` package, whose parity
gate (`scripts/check-algebra-parity.sh` in `pure-algebra/lean4-effects`) freezes the package's
shape. It imports the package and nothing of `Effect4`.
-/

set_option autoImplicit false

namespace Effect4.Laws.Effects

open _root_.Effects

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

/-- **The restriction law.** Interpreting a left-injected program under any handler of the sum
is interpreting it under the handler's left restriction. No monad law is used. -/
theorem interpret_inl_restrict (h : Handler (Signature.sum S T) M) {A : Type uAns}
    (p : Program S A) : interpret h (Program.inl p) = interpret (restrictL h) p := by
  have e := interpret_inl (restrictL h) (restrictR h) p
  rw [← eq_sum_restrict h] at e
  exact e

/-- The restriction law along the right injection. -/
theorem interpret_inr_restrict (h : Handler (Signature.sum S T) M) {A : Type uAns}
    (p : Program T A) : interpret h (Program.inr p) = interpret (restrictR h) p := by
  have e := interpret_inr (restrictL h) (restrictR h) p
  rw [← eq_sum_restrict h] at e
  exact e

end Restriction

section Coproduct

/-- The left injection is a monad morphism into the free monad of the sum. -/
theorem inl_isMonadMorphism :
    IsMonadMorphism S (M := Program (Signature.sum S T)) (fun p => Program.inl p) where
  pure_law _ := rfl
  bind_law p k := Program.inl_bind p k

/-- The right injection is a monad morphism into the free monad of the sum. -/
theorem inr_isMonadMorphism :
    IsMonadMorphism T (M := Program (Signature.sum S T)) (fun p => Program.inr p) where
  pure_law _ := rfl
  bind_law p k := Program.inr_bind p k

variable {M : Type uAns → Type v} [Monad M]

/-- The copairing of two maps out of the free monads: interpretation by the sum of the handlers
their single operations induce. -/
def copair (f : {A : Type uAns} → Program S A → M A) (g : {A : Type uAns} → Program T A → M A) :
    {A : Type uAns} → Program (Signature.sum S T) A → M A :=
  fun p => interpret (Handler.sum ⟨fun op => f (Program.perform op)⟩
    ⟨fun op => g (Program.perform op)⟩) p

/-- **The sum of free theories is the coproduct of the free monads.** For monad morphisms
`f : Program S → M` and `g : Program T → M` into a lawful monad, `copair f g` is a monad
morphism out of `Program (S ⊕ₛ T)`, restricts to `f` along `inl` and to `g` along `inr`, and is
the only monad morphism that does. -/
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

end Effect4.Laws.Effects
