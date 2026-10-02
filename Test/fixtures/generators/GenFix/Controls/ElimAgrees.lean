import GenFix.ValElim

/-!
# The `elim` kind against the hand companions it replaces (a generator fixture)

`tools/Effect4Gen/Fold.lean --kind Effect4.Store.Val=elim:GenFixVal.Val` writes the nested
companions of `Store.Val` under the prefix `GenFixVal`, beside the hand ones of
`src/Effect4/Store/Carrier/Val.lean` (`Val.ind`, `Val.beq`, `Val.beq_iff`). Probe Q's controls 1
and 2 (`Q/probes/Q1/ElimControls.lean`), kept: the generated eliminator has exactly the hand
statement (the two constants are equal by `rfl`, which elaborates only if their types agree), and
the generated Boolean equality is the hand one as a function.
-/

set_option autoImplicit false

namespace GenFix.Controls

/-- The generated eliminator has the hand eliminator's statement. -/
example : @Effect4.Store.GenFixVal.Val.ind = @Effect4.Store.Val.ind := rfl

/-- The generated equality is the hand one. -/
theorem val_beq_agrees (a b : Effect4.Store.Val) :
    Effect4.Store.GenFixVal.Val.beq a b = Effect4.Store.Val.beq a b := by
  rw [Bool.eq_iff_iff, Effect4.Store.GenFixVal.Val.beq_iff, Effect4.Store.Val.beq_iff]

end GenFix.Controls

#print axioms GenFix.Controls.val_beq_agrees
