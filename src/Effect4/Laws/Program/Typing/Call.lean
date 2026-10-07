import Effect4.Program.Typing.Call
import Effect4.Laws.Program.Typing.Focus
import Effect4.Laws.Program.Typing.Sound

/-!
# Program.Typing.Call — the law of the call instance

Slice H9 of `docs/research/2026-10-07-packet-host-meaning.md`. `callAt_rowTy`: where `callAt`
(`Program/Typing/Call.lean`) answers, the node at the address is a call, and the row check at
the request's type answers the instance's columns. The claim `call-instance-address` points at
it.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-- **The call instance is the row check's answer at the request's type.** Where `callAt`
answers, the node at the address is a `perform` of the instance's operation. The request has
the instance's request type in the environment at the address. The row check at that type
answers the instance's two columns. -/
theorem callAt_rowTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {c : CallInstance Op} (h : callAt s env0 p path = some c) :
    ∃ (request : Term) (env : TyEnv) (t : EffTy),
      (Node.eff p).at_ path = some (.eff (.perform c.op request)) ∧
      (Node.eff p).envAt s (.env env0) path = some (.env env) ∧
      termTy s env request = some c.request ∧
      rowTy (s.rowOf c.op) c.request (s.termUse env c.op) = some t ∧
      t.answer = c.answer ∧ t.error = c.error := by
  unfold callAt at h
  obtain ⟨focus, hfocus, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hat, henv, hty⟩ := focusAt_eq_some.mp hfocus
  split at hrest
  · rename_i op request hprogram
    obtain ⟨requestTy, hrequest, hc⟩ := Option.map_eq_some_iff.mp hrest
    cases hc
    rw [hprogram] at hat hty
    have typed := effTy_sound s (.perform op request) focus.env focus.ty hty
    cases typed with
    | perform hdom hterm hrow =>
      have same := Option.some.inj (hterm.symm.trans hrequest)
      subst same
      exact ⟨request, focus.env, focus.ty, hat, henv, hrequest, hrow, rfl, rfl⟩
  · cases hrest

end Effect4.Program
