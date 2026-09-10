import Conform.Spec.Probe1

/-!
# conform-red/Probe2Neg — the red control (outside the `Conform` glob: this file must fail)

A deliberately **wrong** postcondition for the `.branch` arm: it claims the requirement row is
the `then` arm's alone, which is what the printed `Effect.suspend(() => t ? a : b)` head
actually infers on rc.112 (types seat §3.4) and what `effTy` does *not* do. This file must
**fail to compile**; its failure is the evidence that the generated proofs are not vacuous.
Expected: `mvcgen` decomposes the arm and the residual pure goal is unprovable, so `simp_all`
leaves it open and the theorem is refused.
-/

namespace Conform.Spec.Probe2Neg

open Std.Do
open Effect4.Program
open Conform.Spec.Probe1

theorem effTy_branch_wrong {Op : Type} (sig : Signature Op) (env : TyEnv)
    (test : Term) (thenB elseB : Eff Op) :
    ⦃⌜True⌝⦄ effTy sig env (.branch test thenB elseB)
    ⦃(fun t => ⌜∃ a b, effTy sig env thenB = some a ∧ effTy sig env elseB = some b ∧
        t.requires = a.requires⌝,
      fun _ => ⌜True⌝, ())⦄ := by
  simp only [effTy]
  mvcgen [termTy_reflect, effTy_reflect, EffTy.joinAnswer_reflect]
  all_goals simp_all

end Conform.Spec.Probe2Neg
