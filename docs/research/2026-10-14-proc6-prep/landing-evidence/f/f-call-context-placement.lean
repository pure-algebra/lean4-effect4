/-- Context-aware host parking, a step of rows-block-host/R6. Consumer: drive_seg_receipt. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal drive_loop_call_context (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ctx : Ctx)
    (hc : IsCall cur = true) (hk : (stores.budgetOf ctx).2 = true ∨ k + 1 < (stores.budgetOf ctx).1) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
        (M (fiberOf cur K i) s k tr nt ctx) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (Mcall (fiberOf cur K i) s (k + 1) tr' nt ctx) rest 