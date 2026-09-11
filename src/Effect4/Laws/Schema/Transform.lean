import Effect4.Schema.Transform

namespace Effect4.Schema.Transform
open Effect4.Program
open Effect4.Machine.Env (Requirement)
variable {Op : Type} {σ : Signature Op} {Γ : TyEnv}
variable {A B C E₁ E₂ : Ty} {R₁ R₂ : Requirement}

/-- Composition's claimed signature is the actual existing typing judgment. -/
theorem andThen_typed (f : Transform σ Γ A B E₁ R₁) (g : Transform σ Γ B C E₂ R₂) :
    effTy σ (Γ ++ [A]) (f.andThen g).program =
      some ⟨C, E₁.join E₂, R₁.union R₂⟩ := (f.andThen g).typed

/-- The adapted input occupies the appended result slot, including captured prefixes. -/
theorem continuation_input (Γ : TyEnv) :
    Term.weaken Γ.length (.var Γ.length) = .var (Γ.length + 1) := by
  simp [Term.weaken, Var.weaken]
end Effect4.Schema.Transform
