import Effect4.Program.Fold
import Effect4.Machine.Term
import Effect4.Laws.Step.Reading

/-!
# Runtime annotation connector

Placement: helpers of step-language-sound and Queue operation agreement,
translation-simulation, requirement R10, under the Queue migration receipt.
The observation is evalTerm at every value environment.
Record declarations and fold type payloads do not affect this observation.
The connector establishes no typing, membership, admission, or host behavior.
-/

set_option autoImplicit false
namespace Effect4.Program
open Effect4.Store

/-- Erase only payloads that the term evaluator ignores, using the existing Term fold. -/
def Term.annotationEraseAlg : TermAlgebra TermSelfCarrier :=
  { TermAlgebra.id with
    term_record := fun _ names values => .record [] names values
    term_fold := fun _ xs init body => .fold none xs init body }

def Term.eraseAnnotations (t : Term) : Term := cata_term Term.annotationEraseAlg t
def Terms.eraseAnnotations (ts : Terms) : Terms := cata_terms Term.annotationEraseAlg ts

mutual
/-- Removing ignored declarations preserves every evalTerm observation.
The consumer is the Queue message-parameter reading connector. -/
theorem evalTerm_eraseAnnotations : (t : Term) → (env : List Val) →
    evalTerm env t.eraseAnnotations = evalTerm env t
  | .var _, _ => rfl
  | .lit _, _ => rfl
  | .app atom values, env => by
    change evalTerm env (.app atom values.eraseAnnotations) = _
    simp only [evalTerm, evalTerms_eraseAnnotations values env]
  | .record fields names values, env => by
    change evalTerm env (.record [] names values.eraseAnnotations) = _
    simp only [evalTerm, evalTerms_eraseAnnotations values env]
  | .field mode target name, env => by
    change evalTerm env (.field mode target.eraseAnnotations name) = _
    simp only [evalTerm, evalTerm_eraseAnnotations target env]
  | .recordSet target name value, env => by
    change evalTerm env (.recordSet target.eraseAnnotations name value.eraseAnnotations) = _
    simp only [evalTerm, evalTerm_eraseAnnotations target env, evalTerm_eraseAnnotations value env]
  | .tupleAt target index, env => by
    change evalTerm env (.tupleAt target.eraseAnnotations index) = _
    simp only [evalTerm, evalTerm_eraseAnnotations target env]
  | .fold ty xs init body, env => by
    change evalTerm env (.fold none xs.eraseAnnotations init.eraseAnnotations body.eraseAnnotations) = _
    have hb : (fun acc item => evalTerm (env ++ [acc, item]) body.eraseAnnotations) =
        (fun acc item => evalTerm (env ++ [acc, item]) body) := by
      funext acc item
      exact evalTerm_eraseAnnotations body (env ++ [acc, item])
    simp only [evalTerm, evalTerm_eraseAnnotations xs env, evalTerm_eraseAnnotations init env, hb]
/-- The list form serves the app and record cases of evalTerm_eraseAnnotations. -/
theorem evalTerms_eraseAnnotations : (ts : Terms) → (env : List Val) →
    evalTerms env ts.eraseAnnotations = evalTerms env ts
  | .nil, _ => rfl
  | .cons head tail, env => by
    change evalTerms env (.cons head.eraseAnnotations tail.eraseAnnotations) = _
    simp only [evalTerms, evalTerm_eraseAnnotations head env, evalTerms_eraseAnnotations tail env]
end
mutual
/-- Erasure commutes with scope insertion, including a captured term's own fold binders.
The consumer is captured-source annotation agreement in Queue's parameter connector. -/
theorem Term.eraseAnnotations_weaken : (t : Term) → (cut : Nat) →
    (Term.weaken cut t).eraseAnnotations = Term.weaken cut t.eraseAnnotations
  | .var _, _ => rfl
  | .lit _, _ => rfl
  | .app atom values, cut => by
    change Term.app atom (Terms.weaken cut values).eraseAnnotations =
      Term.app atom (Terms.weaken cut values.eraseAnnotations)
    rw [Terms.eraseAnnotations_weaken values cut]
  | .record _ names values, cut => by
    change Term.record [] names (Terms.weaken cut values).eraseAnnotations =
      Term.record [] names (Terms.weaken cut values.eraseAnnotations)
    rw [Terms.eraseAnnotations_weaken values cut]
  | .field mode target name, cut => by
    change Term.field mode (Term.weaken cut target).eraseAnnotations name =
      Term.field mode (Term.weaken cut target.eraseAnnotations) name
    rw [Term.eraseAnnotations_weaken target cut]
  | .recordSet target name value, cut => by
    change Term.recordSet (Term.weaken cut target).eraseAnnotations name (Term.weaken cut value).eraseAnnotations =
      Term.recordSet (Term.weaken cut target.eraseAnnotations) name (Term.weaken cut value.eraseAnnotations)
    rw [Term.eraseAnnotations_weaken target cut, Term.eraseAnnotations_weaken value cut]
  | .tupleAt target index, cut => by
    change Term.tupleAt (Term.weaken cut target).eraseAnnotations index =
      Term.tupleAt (Term.weaken cut target.eraseAnnotations) index
    rw [Term.eraseAnnotations_weaken target cut]
  | .fold _ xs init body, cut => by
    change Term.fold none (Term.weaken cut xs).eraseAnnotations (Term.weaken cut init).eraseAnnotations
      (Term.weaken cut body).eraseAnnotations =
      Term.fold none (Term.weaken cut xs.eraseAnnotations) (Term.weaken cut init.eraseAnnotations)
        (Term.weaken cut body.eraseAnnotations)
    rw [Term.eraseAnnotations_weaken xs cut, Term.eraseAnnotations_weaken init cut,
      Term.eraseAnnotations_weaken body cut]
/-- The list form serves Term.eraseAnnotations_weaken. -/
theorem Terms.eraseAnnotations_weaken : (ts : Terms) → (cut : Nat) →
    (Terms.weaken cut ts).eraseAnnotations = Terms.weaken cut ts.eraseAnnotations
  | .nil, _ => rfl
  | .cons head tail, cut => by
    change Terms.cons (Term.weaken cut head).eraseAnnotations (Terms.weaken cut tail).eraseAnnotations =
      Terms.cons (Term.weaken cut head.eraseAnnotations) (Terms.weaken cut tail.eraseAnnotations)
    rw [Term.eraseAnnotations_weaken head cut, Terms.eraseAnnotations_weaken tail cut]
end

/-- Equal erased trees have equal evaluations, at every value environment. -/
theorem evalTerm_eq_of_annotations {a b : Term} (same : a.eraseAnnotations = b.eraseAnnotations)
    (env : List Val) : evalTerm env a = evalTerm env b := by
  rw [← evalTerm_eraseAnnotations a env, ← evalTerm_eraseAnnotations b env, same]
end Effect4.Program

namespace Effect4.Modules
open Effect4.Program Effect4.Program.Authoring Effect4.Store

/-- Transfer a reading between sources whose successful trees agree after annotation erasure.
The source outcome equality also retains refusal, rather than assuming target success. -/
theorem Reads.of_annotations {source target : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} {v : Val} (read : Reads source env path vals v)
    (same : (target env path).map Term.eraseAnnotations = (source env path).map Term.eraseAnnotations) :
    Reads target env path vals v := by
  obtain ⟨t, sourceTree, value⟩ := read
  cases targetTree : target env path with
  | error fault =>
    rw [targetTree, sourceTree] at same
    nomatch same
  | ok u =>
    rw [targetTree, sourceTree] at same
    injection same with same
    exact ⟨u, targetTree, (evalTerm_eq_of_annotations same vals).trans value⟩
end Effect4.Modules
