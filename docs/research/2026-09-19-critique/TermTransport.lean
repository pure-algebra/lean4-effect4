import Effect4.Program.Typing

/-!
Research candidate: exact evaluation transport under the existing absolute-position
weakening. No typing or scoping hypotheses: out-of-range lookup remains out of range.

The generic lookup statement already exists privately in Program/Typing/Rules.lean.
This standalone experiment restates it because a private declaration is not a public
module interface. Promotion should expose that shared fact once, not keep two copies.
The term proofs use the existing mutually generated Term/Terms recursor through their
ordinary structural equations, exactly as argTy_weaken/argsTy_weaken already do.
-/

namespace CritiqueTermTransport

open Effect4.Machine Effect4.Program

/-- Inserting a slot commutes with lookup at the shifted absolute position. -/
theorem lookup_weaken {α : Type} (pre post : List α) (inserted : α) (index : Nat) :
    (pre ++ inserted :: post)[Var.weaken pre.length index]? = (pre ++ post)[index]? := by
  unfold Var.weaken
  split
  · rename_i h
    simp only [List.getElem?_append_left h]
  · rename_i h
    have hi : pre.length ≤ index := Nat.le_of_not_gt h
    rw [List.getElem?_append_right (Nat.le_trans hi (Nat.le_succ index)),
      List.getElem?_append_right hi, Nat.succ_sub hi, List.getElem?_cons_succ]

mutual
  /-- Evaluation is unchanged by inserting an unused slot, including failed evaluation. -/
  theorem evalTerm_weaken (pre post : List Val) (inserted : Val) (term : Term) :
      evalTerm (pre ++ inserted :: post) (term.weaken pre.length) =
        evalTerm (pre ++ post) term :=
    match term with
    | .var index => lookup_weaken pre post inserted index
    | .lit _ => rfl
    | .app atom args => by
      simp only [Term.weaken, evalTerm, evalTerms_weaken pre post inserted args]

  /-- The same exact transport for an atom's argument spine. -/
  theorem evalTerms_weaken (pre post : List Val) (inserted : Val) (terms : Terms) :
      evalTerms (pre ++ inserted :: post) (terms.weaken pre.length) =
        evalTerms (pre ++ post) terms :=
    match terms with
    | .nil => rfl
    | .cons head tail => by
      simp only [Terms.weaken, evalTerms, evalTerm_weaken pre post inserted head,
        evalTerms_weaken pre post inserted tail]
end

#print axioms lookup_weaken
#print axioms evalTerm_weaken
#print axioms evalTerms_weaken

end CritiqueTermTransport
