import Effect4.Laws.Program.Eliminators
import Effect4.Laws.Program.TypeAlgebra
import Test.Program.UnionRule

/-!
# The order of a lifted rule in Lean core's classes (slice ORDER): the controls

`Laws/Program/Order.lean` states what Lean core's order classes give a join.
`Laws/Program/UnionRule.lean` reads the order of the union combinator in those classes. These
controls give each new statement a reader, and they show where the antisymmetric form stops.

* **Green (proved): a carrier in core's classes is a carrier of answers.** The canonical types
  get their `AnswerOrder` from `AnswerOrder.ofCore`, with two facts.
* **Green (proved): the join law is an equation at the canonical types**, and at a pair of
  them, from antisymmetry alone (`lift_union_eq_of_antisymm`, `prod_antisymm`).
* **Red (tested): the checker's order on raw types is not antisymmetric.** `nat | nat` and `nat`
  are each below the other, and they are two raw types. So the equation at raw types is no case
  of the antisymmetric form: it needs the normal forms.
* **Green (proved, tested): the join law is an equation at a pair of raw types**, at the fiber
  rule's member rule (`lift_union_eq_pair`), with its two sides on two fiber types.
* **Green (proved): the adjoint form in `≤`**, at the list rule: the lifted answer is below a
  type exactly when the target is below the list of that type.

No line restates a theorem, and no line prints axioms. The kernel holds each statement, and the
axiom gate reads every declaration of the tree (`Test/Audit/AxiomGate.lean`).
-/

set_option autoImplicit false

namespace Effect4.Test.Order

open Effect4 Effect4.Program Effect4.Program.UnionRule

/-! ## A carrier in core's classes -/

/-- The canonical types as a carrier of answers: the least answer is `never`, and the join is
the join of their order. -/
instance : Answer CTy where
  bot := CTy.never
  join := max

/-- The order of that carrier, from core's classes: `join = max` by definition, and `never` is
least. -/
instance : AnswerOrder CTy := AnswerOrder.ofCore (fun _ _ => rfl) CTy.never_le

-- green (proved): the join law is an equation at the canonical types, by antisymmetry alone
example {rule : Ty → Option CTy} (mono : Below rule rule) (s t : Ty) :
    lift rule (.union s t) = (lift rule s).bind fun a => (lift rule t).map (Answer.join a) :=
  lift_union_eq_of_antisymm (fun _ _ h1 h2 => Std.IsPartialOrder.le_antisymm _ _ h1 h2) mono s t

-- green (proved): and at a pair of canonical types
example {rule : Ty → Option (CTy × CTy)} (mono : Below rule rule) (s t : Ty) :
    lift rule (.union s t) = (lift rule s).bind fun a => (lift rule t).map (Answer.join a) :=
  lift_union_eq_of_antisymm
    (prod_antisymm (fun _ _ h1 h2 => Std.IsPartialOrder.le_antisymm _ _ h1 h2)
      (fun _ _ h1 h2 => Std.IsPartialOrder.le_antisymm _ _ h1 h2)) mono s t

/-! ## Raw types: no antisymmetry, and the equation still holds -/

-- red (tested): two raw types, each below the other in the checker's order
#guard Ty.subN (.union .nat .nat) .nat && Ty.subN .nat (.union .nat .nat)
#guard Ty.union .nat .nat != .nat

-- green (proved): the join law is an equation at a pair of raw types, at the fiber rule's
-- member rule
example (s t : Ty) :
    lift Member.fiber (.union s t) =
      (lift Member.fiber s).bind fun a => (lift Member.fiber t).map (Answer.join a) :=
  lift_union_eq_pair Member.fiber_eliminator.monotone s t

-- tested: its two sides, on two fiber types with no order
#guard lift Member.fiber (.union (.fiberOf .nat .never) (.fiberOf .string .unit)) =
  some (Ty.join .nat .string, Ty.join .never .unit)
#guard ((lift Member.fiber (.fiberOf .nat .never)).bind fun a =>
    (lift Member.fiber (.fiberOf .string .unit)).map (Answer.join a)) =
  some (Ty.join .nat .string, Ty.join .never .unit)

/-! ## The adjoint form, in `≤` -/

-- green (proved): at the list rule, the lifted answer is below `b` exactly when the target is
-- below the list of `b`, in the order of canonical types
example (t : Ty) {a : Ty} (typed : lift Member.list t = some a) (b : Ty) :
    CTy.ofRaw a ≤ CTy.ofRaw b ↔ CTy.ofRaw t ≤ CTy.ofRaw (.list b) :=
  (Member.list_eliminator.adjoint_le t).2 typed b

end Effect4.Test.Order
