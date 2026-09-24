import Effect4.Laws.Program.Typed.Residual
set_option autoImplicit false
/-! Slice 5 contract ruling probe (2026-09-23): a `True` postcondition on a row whose answer
flows into a leaf makes the program untypable, because the judgment demands a typed
continuation for every admitted answer. Checked under the protocol judgment the M3a
`TypedProg` conjoined, and under the landed one judgment. `interpR`'s join-all park code is
the witness; the other rows named in the ruling have the same shape. Finite probe. -/
namespace Probe.TruePost
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects
abbrev W := Effect4.Program.Typed.World

/-- The join-all park code as `interpR` installs it: the answer is the leaf. -/
def joinAll (targets : List FiberId) : RProgram :=
  .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)

/-- Under the protocol judgment the M3a program judgment conjoined. -/
theorem joinAll_protocol_untypable (root : NativeEff) (w : W) (targets : List FiberId) :
    ¬ Typed hostOrder (Ψ_S.sum (Ψ_F root)) w (fun w' ex => StrongExit w' (EffTy.pure .nat) ex)
      (joinAll targets) := by
  intro h
  obtain ⟨_, _, next⟩ := Typed.inr_inv h
  have leaf := next w (leHost_refl w) (Val.bool true) trivial
  have exit : StrongExit w (EffTy.pure .nat) (.success (Val.bool true)) :=
    Typed.pure_inv (o := hostOrder) (Ψ := Ψ_S.sum (Ψ_F root))
      (Q := fun w' ex => StrongExit w' (EffTy.pure .nat) ex) (w := w)
      (a := .success (Val.bool true)) leaf
  exact Bool.noConfusion exit.1

/-- Under the landed judgment: the same obstruction, which M6's strengthened post removes. -/
theorem joinAll_untypable (root : NativeEff) (w : W) (targets : List FiberId) :
    ¬ TypedProg root w (EffTy.pure .nat) (joinAll targets) := by
  intro h
  cases h with
  | fiber _ _ _ _ _ _ next =>
    exact Bool.noConfusion (TypedProg.pure_inv (next w (leHost_refl w) (Val.bool true) trivial)).1

#print axioms joinAll_protocol_untypable
#print axioms joinAll_untypable
end Probe.TruePost
