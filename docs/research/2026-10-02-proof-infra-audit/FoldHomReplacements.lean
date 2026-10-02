import Effect4.Program.Refs

/-!
Isolated proof replacements for the four equation shapes reviewed in seat L.
No production declaration is replaced by importing this file.
-/

set_option autoImplicit false

namespace FoldHomReview

open Effect4.Program

theorem foldl_shift {α β : Type} (g : α → α) : ∀ (L : List β) (x : α),
    L.foldl (fun acc _ => g acc) (g x) = g (L.foldl (fun acc _ => g acc) x) := by
  intro L x
  exact List.foldl_hom g (fun _ _ => rfl)

section LayerRounds

variable {Op : Type} (orig : Node Op)

private abbrev lrounds (xs : List Nat) (l : LayerTerm Op) : LayerTerm Op :=
  xs.foldl (fun acc _ => LayerTerm.expandRound orig acc) l

private abbrev erounds (xs : List Nat) (e : Eff Op) : Eff Op :=
  xs.foldl (fun acc _ => Eff.expandRound orig acc) e

theorem lrounds_one : ∀ (C : LayerTerm Op → LayerTerm Op),
    (∀ a, LayerTerm.expandRound orig (C a) = C (LayerTerm.expandRound orig a)) →
    ∀ (xs : List Nat) (a : LayerTerm Op), lrounds orig xs (C a) = C (lrounds orig xs a) := by
  intro C hC xs a
  exact List.foldl_hom C (fun x _ => hC x)

theorem lrounds_body : ∀ (C : Eff Op → LayerTerm Op),
    (∀ e, LayerTerm.expandRound orig (C e) = C (Eff.expandRound orig e)) →
    ∀ (xs : List Nat) (e : Eff Op), lrounds orig xs (C e) = C (erounds orig xs e) := by
  intro C hC xs e
  exact List.foldl_hom C (fun x _ => hC x)

theorem lrounds_mergeAll : ∀ (xs : List Nat) (ls : LayerTerms Op),
    lrounds orig xs (.mergeAll ls) =
      .mergeAll (xs.foldl (fun acc _ => LayerTerms.expandRound orig acc) ls) := by
  intro xs ls
  exact List.foldl_hom LayerTerm.mergeAll (fun _ _ => rfl)

end LayerRounds

#print axioms foldl_shift
#print axioms lrounds_one
#print axioms lrounds_body
#print axioms lrounds_mergeAll

end FoldHomReview
