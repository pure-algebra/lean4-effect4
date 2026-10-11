import Test.Dogfood.Scenario.Atomic

set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program

/-- A `Ref.modify` row makes a modify of a cell, with its term and the environment. -/
theorem modify_inv {f : Term} {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf (.refModifyWith f) env val = some o) : ∃ k, o = .refModify ⟨k⟩ f env := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, NativeOp.refModifyWith.injEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h
