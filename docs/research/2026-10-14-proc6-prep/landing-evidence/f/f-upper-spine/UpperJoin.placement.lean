import Effect4.Laws.Program.Agreement.Calls
set_option autoImplicit false
namespace Effect4.Program.Agreement
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
variable {table : RowTable}
/-- Observational joining of two live positions, allowing a finite shift on each side.
Concept translation-simulation; rows-block-host/R6. Consumer: `Leads` and its composition.
The observation is `RunEnd`, including the exact context at a wait. This asserts no progress. -/
def RunJoinC {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (r : σ) (fr' : NFiber) (s' : Stores) (r' : σ)
    (ctx : Ctx := emptyCtx) (ctx' : Ctx := ctx) : Prop :=
  ∃ a b, ∀ n, localRunC host root (n + a) fr s r ctx = localRunC host root (n + b) fr' s' r' ctx'
@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunJoinC.refl {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (fr : NFiber) (s : Stores) (r : σ) (ctx : Ctx) : RunJoinC host root fr s r fr s r ctx ctx
@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunJoinC.trans {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr₁ fr₂ fr₃ : NFiber} {s₁ s₂ s₃ : Stores} {r₁ r₂ r₃ : σ} {ctx₁ ctx₂ ctx₃ : Ctx}
    (h₁ : RunJoinC host root fr₁ s₁ r₁ fr₂ s₂ r₂ ctx₁ ctx₂)
    (h₂ : RunJoinC host root fr₂ s₂ r₂ fr₃ s₃ r₃ ctx₂ ctx₃) :
    RunJoinC host root fr₁ s₁ r₁ fr₃ s₃ r₃ ctx₁ ctx₃
@[semantics "translation-simulation" (requirement := R6)]
proof_goal ReachesC.join {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr' : NFiber} {s s' : Stores} {r r' : σ} {ctx ctx' : Ctx}
    (h : ReachesC host root c fr s r fr' s' r' ctx ctx') :
    RunJoinC host root fr s r fr' s' r' ctx ctx'
@[semantics "translation-simulation" (requirement := R6)]
proof_goal RunJoinC.terminal {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {fr fr' : NFiber} {s s' : Stores} {r r' : σ} {ctx ctx' : Ctx} {c : Nat} {e : RunEnd σ}
    (h : RunJoinC host root fr s r fr' s' r' ctx ctx')
    (ht : localRunC host root c fr' s' r' ctx' = some e) :
    ∃ n, localRunC host root n fr s r ctx = some e
end Effect4.Program.Agreement
