import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Machine.Book

/-!
Checked contract experiments, not a new runtime representation or library API.
The composition theorem reuses the existing syntax, typing judgment and weakening law.
The observation and behavior lemmas state the premises a later connector must discharge.
-/

set_option autoImplicit false

namespace CritiqueContracts
open Effect4 Effect4.Program Conform.Effect4.Typing

/-- Compose two open programs at a shared context. The second program expects
the first answer at the context boundary; insertion skips the retained input. -/
def composeAt {Op : Type} (context : TyEnv) (p q : Eff Op) : Eff Op :=
  .bind p (q.weaken context.length)

theorem composeAt_typed {Op : Type} (sig : Signature Op) (context : TyEnv)
    (input : Ty) (p q : Eff Op) (first second : EffTy)
    (hp : HasTy sig (context ++ [input]) p first)
    (hq : HasTy sig (context ++ [first.answer]) q second) :
    HasTy sig (context ++ [input]) (composeAt context p q)
      ⟨second.answer, first.error.join second.error,
        first.requires.union second.requires⟩ := by
  apply HasTy.bind hp
  have hw := (hasTy_weaken sig context [first.answer] input q second).mpr hq
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using hw

/-- An information order requires an actual forgetful function. No order among
semantic, holder and diagnostic names is assumed. -/
def Factors {State Fine Coarse : Type} (fine : State → Fine)
    (coarse : State → Coarse) : Prop :=
  ∃ forget : Fine → Coarse, ∀ s, coarse s = forget (fine s)

theorem Factors.respects_eq {State Fine Coarse : Type}
    {fine : State → Fine} {coarse : State → Coarse}
    (h : Factors fine coarse) {a b : State} (same : fine a = fine b) :
    coarse a = coarse b := by
  obtain ⟨forget, h⟩ := h
  exact (h a).trans ((congrArg forget same).trans (h b).symm)

theorem Factors.trans {State A B C : Type} {a : State → A} {b : State → B}
    {c : State → C} (hab : Factors a b) (hbc : Factors b c) : Factors a c := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  exact ⟨g ∘ f, fun s => (hg s).trans (congrArg g (hf s))⟩

/-- Implementation-to-specification behavior matching is the direction needed
to transfer a universal safety property. Realization of source behaviors alone
does not exclude additional bad target behaviors. -/
theorem transfer_safety {Source Target : Type}
    (source : Source → Prop) (target : Target → Prop)
    (related : Source → Target → Prop)
    (goodSource : Source → Prop) (goodTarget : Target → Prop)
    (matching : ∀ t, target t → ∃ s, source s ∧ related s t)
    (safe : ∀ s, source s → goodSource s)
    (respects : ∀ s t, related s t → goodSource s → goodTarget t) :
    ∀ t, target t → goodTarget t := by
  intro t ht
  obtain ⟨s, hs, hr⟩ := matching t ht
  exact respects s t hr (safe s hs)

-- A finite countermodel for the reverse implication: the implementation has
-- every source behavior and one additional bad behavior.
def onlyZero (n : Nat) : Prop := n = 0
def zeroOrOne (n : Nat) : Prop := n = 0 ∨ n = 1

theorem reverse_inclusion_holds : ∀ n, onlyZero n → zeroOrOne n :=
  fun _ h => Or.inl h

theorem reverse_inclusion_does_not_transfer_safety :
    ¬ (∀ n, zeroOrOne n → onlyZero n) := by
  intro h
  have bad : 1 = 0 := h 1 (Or.inr rfl)
  cases bad

-- Reuse this existing lemma when lifting a related operation through a journal;
-- the local simulation premise, choice relation and observation remain owed.
#check Effect4.Machine.foldl_rel

#print axioms composeAt_typed
#print axioms Factors.respects_eq
#print axioms Factors.trans
#print axioms transfer_safety
#print axioms reverse_inclusion_holds
#print axioms reverse_inclusion_does_not_transfer_safety

end CritiqueContracts
