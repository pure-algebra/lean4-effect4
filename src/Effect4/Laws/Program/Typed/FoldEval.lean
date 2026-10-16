import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Typed.Adequacy

/-!
# Laws.Program.Typed.FoldEval — a term's evaluation under an inserted slot, a refusing step, and one atomic step

Concept: Store Typing (`store-typing`). Requirement: R4. Three steps of the registry claim
`fold-typed-atomic-update`, whose statement is `fold_typed_atomic_update`
(`src/Effect4/Laws/Program/Typed/ListFold.lean`):

* `evalTerm_weaken`: inserting one slot at a cut keeps a term's whole evaluation, refusal
  included, a fold's body among them;
* `foldlM_refuses`: a refusing step refuses the whole fold;
* `refModify_typed_step`: a `Ref.modify` whose term the checker types is one store step.

They read no printer and no reader, so they stand apart from the claim's statement, which holds
the printed equations of the leaf. Their other consumers read them here: the step terms' typing
(`src/Effect4/Laws/Step.lean`) reads `evalTerm_weaken`, and the store law of a step
(`step_keeps_cell`, `src/Effect4/Laws/Step/Store.lean`) reads `refModify_typed_step`, the claim's
`step` field.

What they do not establish: no statement about a body that the checker refuses, no agreement
with a target, and no progress of a scheduler.
-/

set_option autoImplicit false

/-! ## Evaluation under an inserted slot, and a refusing step -/

namespace Effect4.Program
open Effect4 Effect4.Machine

mutual
  /-- **Weakening of evaluation**: inserting one slot at a cut, with every variable at or above
  the cut moved up, keeps the whole result of a term's evaluation, refusal included. A fold
  needs no case of its own beyond its body's: the body's environment gains the two binders
  after the inserted slot, and the cut stays the prefix's length, so the same statement holds
  under them. A step of `fold-typed-atomic-update` (R4), beside the typing's `argTy_weaken`. -/
  theorem evalTerm_weaken (pre post : List Val) (inserted : Val) (term : Term) :
      evalTerm (pre ++ inserted :: post) (Term.weaken pre.length term) =
        evalTerm (pre ++ post) term :=
    match term with
    | .var index => lookup_weaken pre post inserted index
    | .lit _ => rfl
    | .app atom args => by
      simp only [Term.weaken, evalTerm, evalTerms_weaken pre post inserted args]
    | .record fields names values => by
      simp only [Term.weaken, evalTerm, evalTerms_weaken pre post inserted values]
    | .field mode target name => by
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted target]
    | .recordSet target name value => by
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted target,
        evalTerm_weaken pre post inserted value]
    | .tupleAt target index => by
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted target]
    | .fold accTy list init body => by
      have hbody : ∀ acc item : Val,
          evalTerm ((pre ++ inserted :: post) ++ [acc, item]) (Term.weaken pre.length body) =
            evalTerm ((pre ++ post) ++ [acc, item]) body := fun acc item => by
        rw [List.append_assoc, List.cons_append, List.append_assoc]
        exact evalTerm_weaken pre (post ++ [acc, item]) inserted body
      simp only [Term.weaken, evalTerm, evalTerm_weaken pre post inserted list,
        evalTerm_weaken pre post inserted init, hbody]

  theorem evalTerms_weaken (pre post : List Val) (inserted : Val) (terms : Terms) :
      evalTerms (pre ++ inserted :: post) (Terms.weaken pre.length terms) =
        evalTerms (pre ++ post) terms :=
    match terms with
    | .nil => rfl
    | .cons head tail => by
      simp only [Terms.weaken, evalTerms, evalTerm_weaken pre post inserted head,
        evalTerms_weaken pre post inserted tail]
end

/-- **A refusing step refuses the fold**: where the steps before an element answer and the
element's step refuses, the fold over the whole list refuses. No partial answer exists. -/
theorem foldlM_refuses {α β : Type} (step : β → α → Option β) :
    ∀ (xs ys : List α) (x : α) (acc a : β), xs.foldlM step acc = some a → step a x = none →
      (xs ++ x :: ys).foldlM step acc = none
  | [], ys, x, acc, a, h, hx => by
    have h' : some acc = some a := h
    cases h'
    show (step acc x).bind (fun next => ys.foldlM step next) = none
    rw [hx]
    rfl
  | y :: xs, ys, x, acc, a, h, hx => by
    have h' : (step acc y).bind (fun next => xs.foldlM step next) = some a := h
    obtain ⟨next, hnext, hrest⟩ := Option.bind_eq_some_iff.mp h'
    show (step acc y).bind (fun next => (xs ++ x :: ys).foldlM step next) = none
    rw [hnext]
    exact foldlM_refuses step xs ys x next a hrest hx

end Effect4.Program

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program

/-! ## One atomic step -/

/-- **One atomic step.** A `Ref.modify` whose term the checker types at the node's environment
extended by the cell's type `A`, with the pair type of `B` and `A`, is one store step. At a
store whose cell holds a member `a` of `A`, the step reads the cell once and evaluates the term
once, at `env ++ [a]`. It answers the pair's first component, a member of `B`, and leaves the
second, a member of `A`, in the cell. The term may hold a fold: the whole fold is inside the
one evaluation. The term's map is `termMaps_of_typed`, and the step is the census clause
`refStep_modify`. It reads the fixed world `w` and no later one. -/
theorem refModify_typed_step {sig : Signature NativeOp} (hatom : sig.atomOf = nativeAtomTy)
    (htypes : sig.types = []) {w : World} {tys : TyEnv} {env : List Val} (henv : EnvTyped w tys env) {f : Term}
    {A B : Ty} (hty : termTy sig (tys ++ [A]) f = some (.prod B A)) {s : Stores}
    {cell : RefKey} {a : Val} (hcell : refPeek s.refs cell = some a) (ha : Fits w a A) :
    ∃ b a', evalTerm (env ++ [a]) f = some (Val.tuple [b, a']) ∧
      syncOpStep (.refModify cell f env) s =
        some ({ s with refs := refPoke s.refs cell a' }, b) ∧
      Fits w b B ∧ Fits w a' A := by
  obtain ⟨r, hr, hfit⟩ := termMaps_of_typed hatom htypes henv hty w (leHost_refl w) a ha
  obtain ⟨b, a', rfl, hb, ha'⟩ := (fits_prod_iff w r B A).mp hfit
  refine ⟨b, a', hr, ?_, hb, ha'⟩
  show (refStep (.refModify cell f env) s.refs).map
    (fun step => ({ s with refs := step.2 }, step.1)) = _
  rw [refStep_modify s.refs cell f env a b a' hcell hr]
  rfl

end Effect4.Program.Typed
