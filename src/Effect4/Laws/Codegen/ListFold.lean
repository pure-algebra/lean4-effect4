import Effect4.Codegen.ListFold
import Effect4.Codegen.Record
import Effect4.Codegen.Tuple
import Effect4.Codegen.Classes

/-!
# Laws.Codegen.ListFold — the list fold's image, exact (decisions row 228)

Concept: Exact Codecs (`exact-codecs`), serving `fold-typed-atomic-update` (R4) through the
leaf's printed and read equations. These are the steps of the fold cases of
`readTerm_printTerm` and `readTerm_exact` (`Laws/Codegen/ReadLeaf.lean`), whose consumers are
`read_print` and `read_exact` (R8).

Reach: every level and every expression. The retraction holds at the image without a type
argument, the only image the reader accepts: a stated accumulator type is printed and not read
(B19). `Binders` holds at every list of binder slots, so the state plan's T5 reads its
one-parameter function through the same two laws.

What they do not establish: that tsgo accepts a printed fold or that the prelude's `fold`
computes the model's answer. Both are finite host checks (`ts/eff/test`, the truth lane).
-/

set_option autoImplicit false

namespace Effect4.Codegen.Binders
open TypeScript

/-- Retraction: a function of binders reads back to its body. -/
theorem read_write (n : Nat) (bs : List Nat) (body : Expr) :
    read n bs (write n bs body) = some body := by
  simp only [write, read, ↓reduceIte]

/-- Exactness: what reads as a function of these binders is that function. -/
theorem read_exact (n : Nat) (bs : List Nat) (e body : Expr) (h : read n bs e = some body) :
    write n bs body = e := by
  unfold read at h
  split at h
  · next ps body' =>
    split at h
    · next hps =>
      cases h
      simp only [write, hps]
    · exact nomatch h
  · exact nomatch h

end Effect4.Codegen.Binders

namespace Effect4.Codegen.ListFold
open TypeScript

/-- Retraction: the image without a type argument reads back to its three parts. -/
theorem read_write (n : Nat) (list init body : Expr) :
    read n (write n none list init body) = some (list, init, body) := by
  simp only [write, read, ↓reduceIte, Binders.read_write, Option.map_some]

/-- Exactness: what reads as a fold at level `n` is the image without a type argument. -/
theorem read_exact (n : Nat) (e list init body : Expr)
    (h : read n e = some (list, init, body)) : write n none list init body = e := by
  unfold read at h
  split at h
  · next head list' init' step =>
    split at h
    · next hhead =>
      obtain ⟨body', hbody, h⟩ := Option.map_eq_some_iff.mp h
      cases h
      simp only [write, Binders.read_exact n [0, 1] step body hbody, hhead]
    · exact nomatch h
  · exact nomatch h

/-! The fold's image is disjoint from each reader that the term reader tries before it. -/

theorem readClass_write (n : Nat) (list init body : Expr) :
    Classes.readClass (write n none list init body) = none := rfl

theorem readRecord_write (n : Nat) (list init body : Expr) :
    Record.readRecord (write n none list init body) = none := rfl

theorem readField_write (n : Nat) (list init body : Expr) :
    Record.readField (write n none list init body) = none := rfl

theorem readSet_write (n : Nat) (list init body : Expr) :
    Record.readSet (write n none list init body) = none := rfl

theorem readAt_write (n : Nat) (list init body : Expr) :
    Tuple.readAt (write n none list init body) = none := rfl

end Effect4.Codegen.ListFold

namespace Effect4.Program

/-! ## No stated type, node by node (the generated fold's equations)

Steps of `readTerm_printTerm` and of the row lemmas in `Laws/Codegen/ReadLeaf.lean` (R8): the
round trip splits a term that states no accumulator type into its node and its children. -/

theorem Term.unannotated_app (atom : String) (args : Terms) :
    Term.unannotated (.app atom args) = Terms.unannotated args := rfl
theorem Term.unannotated_record (fields : List (String × Bool × Ty)) (names : List String)
    (values : Terms) :
    Term.unannotated (.record fields names values) = Terms.unannotated values := rfl
theorem Term.unannotated_field (mode : FieldReadMode) (target : Term) (name : String) :
    Term.unannotated (.field mode target name) = Term.unannotated target := rfl
theorem Term.unannotated_recordSet (target : Term) (name : String) (value : Term) :
    Term.unannotated (.recordSet target name value) =
      (Term.unannotated target && Term.unannotated value) := rfl
theorem Term.unannotated_tupleAt (target : Term) (index : Nat) :
    Term.unannotated (.tupleAt target index) = Term.unannotated target := rfl
/-- A fold states no type exactly when its own type is absent and its three children state
none. -/
theorem Term.unannotated_fold (accTy : Option Ty) (list init body : Term) :
    Term.unannotated (.fold accTy list init body) =
      (accTy.isNone &&
        (Term.unannotated list && (Term.unannotated init && Term.unannotated body))) := by
  cases accTy <;> rfl
theorem Terms.unannotated_cons (t : Term) (ts : Terms) :
    Terms.unannotated (.cons t ts) = (Term.unannotated t && Terms.unannotated ts) := rfl

theorem CauseTerm.unannotated_fail (t : Term) :
    CauseTerm.unannotated (.fail t) = Term.unannotated t := rfl
theorem CauseTerm.unannotated_die (t : Term) :
    CauseTerm.unannotated (.die t) = Term.unannotated t := rfl
theorem CauseTerm.unannotated_interrupt (who : Option Term) :
    CauseTerm.unannotated (.interrupt who) = who.all Term.unannotated := rfl
theorem CauseTerm.unannotated_both (left right : CauseTerm) :
    CauseTerm.unannotated (.both left right) =
      (CauseTerm.unannotated left && CauseTerm.unannotated right) := rfl

end Effect4.Program
