/-! These helpers serve `drive_seg_receipt`, rows-block-host/R6.
They transport actual finite receipts and exact local observations.
They provide no command bound or scheduler progress. -/



@[semantics "translation-simulation" (requirement := R6)]
proof_goal drive_receipt_stable (root : NativeEff) (fuel : Nat) (m : Api.Machine)
    (cmds : List NCmd)
    (h : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel m cmds) = true) (k : Nat) :
    driveState (evaluator := evaluatorFor root table) (interpOf root table) (fuel + k) m cmds =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds 

@[semantics "translation-simulation" (requirement := R6)]
proof_goal drive_receipt_prefix (root : NativeEff) (fuel a : Nat) (m m' : Api.Machine)
    (cmds cmds' : List NCmd)
    (h : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel m cmds) = true)
    (hn : settled (m', cmds') = false)
    (hp : ∀ n, driveState (evaluator := evaluatorFor root table)
      (interpOf root table) (n + a) m cmds =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n m' cmds') :
    ∃ rest, fuel = rest + a ∧
      driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds =
        driveState (evaluator := evaluatorFor root table) (interpOf root table) rest m' cmds' 

@[semantics "translation-simulation" (requirement := R6)]
proof_goal drive_receipt_result (root : NativeEff) (fuel a : Nat) (m result : Api.Machine)
    (cmds : List NCmd)
    (h : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel m cmds) = true)
    (hp : ∀ n, driveState (evaluator := evaluatorFor root table)
      (interpOf root table) (n + a) m cmds = (result, [])) :
    driveState (evaluator := evaluatorFor root table) (interpOf root table) fuel m cmds =
      (result, []) 

@[semantics "translation-simulation" (requirement := R6)]
proof_goal ContextSegOwes.prepend {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    {ctx ctx' : Ctx} {result : Api.Machine} {c : Nat}
    (hr : ReachesQ (table := table) root c fr s fr' s' ctx ctx')
    (ho : ContextSegOwes root table fr' s' ctx' result) :
    ContextSegOwes root table fr s ctx result 

@[semantics "translation-simulation" (requirement := R6)]
proof_goal context_run_finish {σ : Type} {host : Effects.Comodel (RowSig table) σ}
    {root : NativeEff} {fr : NFiber} {s s' : Stores} {ctx ctx' : Ctx} {ex : ExitV}
    (h : contextStep root fr s ctx = (.finished ex s', ctx'))
    (hc : IsCall fr.current = false) (r : σ) :
    localRunC host root 1 fr s r ctx = some (.exit ex s' r) 

@[semantics "translation-simulation" (requirement := R6)]
proof_goal context_receipt_finish (root : NativeEff) (fuel : Nat) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (ctx : Ctx) (d : Bool)
    (ex : ExitV) (ctx' : Ctx) (fr' : NFiber) (k' : Nat) (tr' : NTrace)
    (hq : Quiet s) (hstep : contextStep root (fiberOf cur K i) s ctx = (.finished ex s, ctx'))
    (hc : IsCall cur = false)
    (hdrv : ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      (n + 1) (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (M fr' s k' tr' nt ctx') [Cmd.finish Api.root ex, Cmd.drainDue])
    (hreceipt : settled (driveState (evaluator := evaluatorFor root table)
      (interpOf root table) fuel (M (fiberOf cur K i) s k tr nt ctx)
      [cmdOf d, Cmd.drainDue]) = true) :
    ∃ result, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      fuel (M (fiberOf cur K i) s k tr nt ctx) [cmdOf d, Cmd.drainDue] = (result, []) ∧
      ContextSegOwes root table (fiberOf cur K i) s ctx result 