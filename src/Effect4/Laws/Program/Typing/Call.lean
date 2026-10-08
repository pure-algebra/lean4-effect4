import Effect4.Program.Typing.Call
import Effect4.Laws.Program.Typing.Focus
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Auto.Semantics

/-!
# Program.Typing.Call — the law of the call instance

Slice H9 of `docs/research/2026-10-07-packet-host-meaning.md`. `callAt_rowTy`: where `callAt`
(`Program/Typing/Call.lean`) answers, the node at the address is a call, and the row check at
the request's type answers the instance's columns. The instance's bindings are the row's at that
type. The claim `call-instance-address` points at it.

`checkRow_rowBindings`: where the row check answers, `rowBindings` answers the substitution that
instantiates the answer's two columns. With `callAt_rowTy` it gives the instance's columns from
its bindings. The consumer is the typed print (slice PRINT, step P2), which writes a call's type
arguments from them.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-- **Where the row check answers, `rowBindings` answers its bindings**: the substitution that
instantiates the answer's two columns. A step of `call-instance-address`. Its consumer is the
typed print (slice PRINT, step P2), with `callAt_rowTy`.

It does not say that the bindings are unique, or what they bind where the row check refuses. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkRow_rowBindings {row : Row} {r : Ty} {use : Option TermUse} {t : EffTy}
    (h : checkRow row r use = .ok t) :
    ∃ σ, rowBindings row r use = some σ ∧ t.answer = (row.answer.instantiate σ).normalize ∧
      t.error = (row.error.instantiate σ).normalize := by
  unfold checkRow at h
  unfold rowBindings
  split at h
  · cases h
  · rename_i σ hσ
    split at h
    · cases h
    · rename_i bindings hbind
      split at h
      · cases h
      · cases h
        exact ⟨bindings, by simp only [hσ, Option.bind_some, hbind, Except.toOption], rfl, rfl⟩

/-- **The call instance is the row check's answer at the request's type.** Where `callAt`
answers, the node at the address is a `perform` of the instance's operation. The request has
the instance's request type in the environment at the address. The row check at that type
answers the instance's two columns, and the instance's bindings are the row's there. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem callAt_rowTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {c : CallInstance Op} (h : callAt s env0 p path = some c) :
    ∃ (request : Term) (env : TyEnv) (t : EffTy),
      (Node.eff p).at_ path = some (.eff (.perform c.op request)) ∧
      (Node.eff p).envAt s (.env env0) path = some (.env env) ∧
      termTy s env request = some c.request ∧
      rowTy (s.rowOf c.op) c.request (s.termUse env c.op) = some t ∧
      t.answer = c.answer ∧ t.error = c.error ∧
      rowBindings (s.rowOf c.op) c.request (s.termUse env c.op) = some c.bindings := by
  unfold callAt at h
  obtain ⟨focus, hfocus, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hat, henv, hty⟩ := focusAt_eq_some.mp hfocus
  split at hrest
  · rename_i op request hprogram
    obtain ⟨requestTy, hrequest, hbound⟩ := Option.bind_eq_some_iff.mp hrest
    obtain ⟨bindings, hbindings, hc⟩ := Option.map_eq_some_iff.mp hbound
    cases hc
    rw [hprogram] at hat hty
    have typed := effTy_sound s (.perform op request) focus.env focus.ty hty
    cases typed with
    | perform hdom hterm hrow =>
      have same := Option.some.inj (hterm.symm.trans hrequest)
      subst same
      exact ⟨request, focus.env, focus.ty, hat, henv, hrequest, hrow, rfl, rfl, hbindings⟩
  · cases hrest

end Effect4.Program
