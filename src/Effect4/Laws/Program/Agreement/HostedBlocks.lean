import Effect4.Laws.Program.Agreement.Blocks
import Effect4.Laws.Program.Agreement.Hosted
import Effect4.Laws.Auto.Semantics

set_option autoImplicit false
namespace Effect4.Program.Agreement
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
variable {table : RowTable}

/-- Step of block-handler-monotone (R10), consumed by `hostRunBlockB_exits`.
An empty parameter list yields a monotone budget chain at every context.
A finished host observation persists; no cut implies progress. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal hostRunBlockB_stable {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (bodies : List NativeEff) {k k' : Nat} (hk : k ≤ k') (e : NativeEff)
    (ctx : Ctx) (env : List Val) (s : Stores) (st : σ) (ex : ExitV) (out : Stores × σ)
    (h : hostRunBlockB host bodies k [] e ctx env s st = some (some ex, out)) :
    hostRunBlockB host bodies k' [] e ctx env s st = some (some ex, out)

/-- Step of `rows-block-host`, R6. Consumer: `hostRunBlockB_exits`.
Reach: a local run from the block root that already exits.
It supplies one finished meaning budget, not termination or scheduler progress. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal localRunC_to_blockB {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hfrag : BlockRows table root = true) (cf : Nat) (R : σ)
    {c : Nat} {ex : ExitV} {s' : Stores} {r' : σ}
    (h : localRunC host root c (fiberOf (compile root cf) []) Stores.empty R =
      some (.exit ex s' r')) :
    ∃ k, hostRunBlockB host (bodiesOf root) k [] root emptyCtx [] Stores.empty R =
      some (some ex, (s', r'))

/-- Step of `rows-block-host`, R6. Consumer: `h9_blocks`.
Reach: a local run already leading to a completed root exit.
Monotonicity retains that exit past a meaning-budget bound. No progress follows. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal hostRunBlockB_exits {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hfrag : BlockRows table root = true) (cf : Nat) (R st : σ)
    {ex : ExitV} {s : Stores}
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R (.done ex s) st) :
    ∃ lower, ∀ k, lower ≤ k →
      hostRunBlockB host (bodiesOf root) k [] root emptyCtx [] Stores.empty R =
        some (some ex, (s, st))
end Effect4.Program.Agreement
