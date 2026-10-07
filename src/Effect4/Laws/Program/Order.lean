import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Order — a join in Lean core's order classes

The estate states an order in Lean core's classes: `LE`, `Max`, `Std.IsPreorder`,
`Std.IsPartialOrder` and `Std.LawfulOrderSup` (`Init/Data/Order/Classes.lean`). The canonical
types and the error types have them (`Laws/Program/TypeAlgebra.lean`), and so have the type slices
(`Laws/Slice/Lattice.lean`). This module holds what those classes give a join, stated once.

* **In a preorder with joins**: core has the two bounds (`Std.left_le_max`, `Std.right_le_max`)
  and the least upper bound as an equivalence (`Std.max_le_iff`). Here: the least upper bound as
  a rule (`max_le`), and the monotone law (`max_mono`).
* **In a partial order with joins**: antisymmetry makes the three equations of a semilattice:
  `max_comm`, `max_idem` and `max_assoc`. Core has them for a linear order only.

No instance of core's operation classes (`Std.Commutative`, `Std.Associative`,
`Std.IdempotentOp`) is declared: nothing of the tree reads one yet. The three equations are
their fields when a reader comes.

Placement (AGENTS.md, Trust): concept subtyping-algebra (`docs/core/semantics.md` §2.6),
requirement R14. Each theorem is a step of the claims `sub-antisymm-canonical` and
`union-rule-lift`. The consumers are the join equations of `CTy` and `ErrTy`
(`Laws/Program/TypeAlgebra.lean`) and `AnswerOrder.ofCore` (`Laws/Program/UnionRule.lean`).
-/

set_option autoImplicit false

namespace Effect4.Order

universe u

/-! ## In a preorder: the least upper bound and the monotone law -/

section Preorder

variable {α : Type u} [LE α] [Max α] [Std.LawfulOrderSup α]

/-- The join is below each upper bound of its two arguments: one direction of core's
`Std.max_le_iff`, as a rule. Its consumers are the laws below and `AnswerOrder.ofCore`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem max_le {a b c : α} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c :=
  Std.max_le_iff.mpr ⟨h1, h2⟩

/-- The join is monotone in both arguments. Its consumer is the `mono` premise of a slice view
of an answer that a join builds (`SliceView`, `Laws/Slice/Lattice.lean`). -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem max_mono [Std.IsPreorder α] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    max a b ≤ max c d :=
  max_le (Std.IsPreorder.le_trans a c _ hac Std.left_le_max)
    (Std.IsPreorder.le_trans b d _ hbd Std.right_le_max)

end Preorder

/-! ## In a partial order: the three equations -/

section PartialOrder

variable {α : Type u} [LE α] [Max α] [Std.IsPartialOrder α] [Std.LawfulOrderSup α]

/-- In a partial order with joins, the join is commutative. Its consumers are `CTy.join_comm`
and `ErrTy.join_comm`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem max_comm (a b : α) : max a b = max b a :=
  Std.IsPartialOrder.le_antisymm _ _
    (max_le Std.right_le_max Std.left_le_max)
    (max_le Std.right_le_max Std.left_le_max)

/-- In a partial order with joins, the join is idempotent. Its consumers are `CTy.join_self`
and `ErrTy.join_self`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem max_idem (a : α) : max a a = a :=
  Std.IsPartialOrder.le_antisymm _ _
    (max_le (Std.IsPreorder.le_refl a) (Std.IsPreorder.le_refl a))
    Std.left_le_max

/-- In a partial order with joins, the join is associative. Its consumers are `CTy.join_assoc`
and `ErrTy.join_assoc`. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem max_assoc (a b c : α) : max (max a b) c = max a (max b c) :=
  Std.IsPartialOrder.le_antisymm _ _
    (max_le
      (max_le Std.left_le_max
        (Std.IsPreorder.le_trans _ _ _ Std.left_le_max Std.right_le_max))
      (Std.IsPreorder.le_trans _ _ _ Std.right_le_max Std.right_le_max))
    (max_le
      (Std.IsPreorder.le_trans _ _ _ Std.left_le_max Std.left_le_max)
      (max_le
        (Std.IsPreorder.le_trans _ _ _ Std.right_le_max Std.left_le_max)
        Std.right_le_max))

end PartialOrder

end Effect4.Order
