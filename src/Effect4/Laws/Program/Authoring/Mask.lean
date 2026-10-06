import Effect4.Program.Authoring.Mask
import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Laws.Program.Author

/-!
# Laws.Program.Authoring.Mask — the mask's builders keep the scope judgment

Decisions rows 244 to 246. The builders of `Program/Authoring/Mask.lean` author the mask as a
derived form over `bind`. Each keeps the authoring scope judgment (`Src.Scoped`), by one
application of the lemmas of the lifts it is made of, and each is named so that
`authoring_scoped` finds it.

Placement. These are the scope rule of the claim `scoped-body-substitution-boundary` (concept
`residual-program-typing`, requirement R4) at the surface an author writes: the mask binds one
name, the saved state, and a restore site binds nothing. Their consumer is a scoped authored
program that masks, the Queue's waiting wrapper first and the Semaphore's protected permit
next. They establish no typing and no behaviour.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

/-- The mask under a written name: the body is scoped one level up, under the saved state's
name. -/
@[semantics "residual-program-typing"]
theorem uninterruptibleMask_scoped {Op : Type} [ScopedOp Op] (saved : String) {body : Src Op}
    (hb : body.Scoped) : (uninterruptibleMask saved body).Scoped :=
  bind_scoped saved (withFiber_scoped Action.getInterruptible_scoped) (uninterruptible_scoped hb)

/-- The hygienic mask: whatever name is minted, the body is scoped when it is scoped for every
restore function that keeps the judgment. The function handed to it does: a restore site binds
nothing, and its saved term is the minted name's reader. -/
@[semantics "residual-program-typing"]
theorem uninterruptibleMaskWith_scoped {Op : Type} [ScopedOp Op]
    {body : (Src Op → Src Op) → Src Op}
    (hb : ∀ restoreSite : Src Op → Src Op,
      (∀ e : Src Op, e.Scoped → (restoreSite e).Scoped) → (body restoreSite).Scoped) :
    (uninterruptibleMaskWith body).Scoped :=
  minting_scoped _ fun saved => uninterruptibleMask_scoped saved
    (hb _ fun _ he => restore_scoped (minted_scoped saved) he)

/-- **The derived form is the program's own expansion**, node for node (the note's F6): the
getter under a `bind` whose rest is the body under `uninterruptible`, the body elaborated one
level up at the path of that node's child 0. No constructor is added for the mask. -/
@[semantics "residual-program-typing"]
theorem uninterruptibleMask_elaborates {Op : Type} (saved : String) (body : Src Op) (env : Env)
    (p : List Nat) (b : Eff Op) (hb : body (env.push [saved]) (p ++ [1] ++ [0]) = .ok b) :
    uninterruptibleMask saved body env p =
      .ok (.bind (.withFiber .getInterruptible) (.uninterruptible b)) := by
  unfold uninterruptibleMask bind withFiber Action.getInterruptible uninterruptible
  rw [hb]
  rfl

end Effect4.Program.Authoring
