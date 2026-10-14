/-- An actual flush receipt settles every completed round at its actual context.
Step of rows-block-host/R6; consumer: `holds_flush`. The resumed wrapper joins its saved code.
No budget restriction, positive-step assumption or progress bound is asserted. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal flush_Myield_receipt (root : NativeEff) (hroot : PlainHooks root) :
    ∀ (rounds : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
      (tr : NTrace) (t : Nat) (fuel : Nat) (ctx : Ctx),
      PlainCode cur = true → PlainStack K → Quiet s →
      (flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel rounds
        (Myield (fiberOf cur K i) s k tr t ctx)).2 = true →
      ∃ p', Settled root (flushAllState (evaluator := evaluatorFor root table)
          (interpOf root table) fuel rounds (Myield (fiberOf cur K i) s k tr t ctx)).1 p' ∧
        LeadsQ (table := table) root (.live (fiberOf cur K i) s ctx) p'

