import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Auto.Obligations

/-! D12's declaration-backed proof ledger for the laws of `Laws/Effects/Protocol.lean`. The
registrations sit here, beside the ledger's users, so the generic Protocol module and its
area import only the pinned `Effects` (moved from `Laws/Effects/` on 2026-09-23). -/
set_option autoImplicit false
namespace Effect4.Laws.Effects.D12
open _root_.Effects
universe u v w
variable {W : Type w} {S : Signature.{u, v}} {A : Type v}

theorem mono {o : WorldOrder W} {Ψ : Protocol W S} {Q : W → A → Prop} {p : Program S A}
    (_hpre : ∀ op cert, Mono o (fun w => Ψ.pre w op cert)) (_hQ : ∀ a, Mono o (fun w => Q w a))
    {w w' : W} (_hle : o.le w w') (_h : Typed o Ψ w Q p) : ProofGraph.Obligation
    (Typed o Ψ w' Q p) := ⟨⟩
#obligation_proved mono := @Effect4.Laws.Effects.Typed.mono

theorem bind {o : WorldOrder W} {Ψ : Protocol W S} {B : Type v}
    {Q : W → A → Prop} {R : W → B → Prop} {p : Program S A} {k : A → Program S B} {w : W}
    (_h : Typed o Ψ w Q p) (_hk : ∀ w' a, Q w' a → Typed o Ψ w' R (k a)) : ProofGraph.Obligation
    (Typed o Ψ w R (p.bind k)) := ⟨⟩
#obligation_proved bind := @Effect4.Laws.Effects.Typed.bind

theorem widen {o : WorldOrder W} {Ψ : Protocol W S} {Q Q' : W → A → Prop}
    {p : Program S A} {w : W} (_h : Typed o Ψ w Q p) (_hQ : ∀ w a, Q w a → Q' w a) : ProofGraph.Obligation
    (Typed o Ψ w Q' p) := ⟨⟩
#obligation_proved widen := @Effect4.Laws.Effects.Typed.widen

theorem inl {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {p : Program S A} {w : W}
    (_h : Typed o Ψ₁ w Q p) : ProofGraph.Obligation
    (Typed o (Ψ₁.sum Ψ₂) w Q p.inl) := ⟨⟩
#obligation_proved inl := @Effect4.Laws.Effects.Typed.inl

theorem inl_inv {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {w : W} {op : S.Op}
    {k : (Signature.sum S T).Answer (.inl op) → Program (Signature.sum S T) A}
    (_h : Typed o (Ψ₁.sum Ψ₂) w Q (.vis (.inl op) k)) : ProofGraph.Obligation
    (∃ cert : Ψ₁.Cert op, Ψ₁.pre w op cert ∧
      ∀ w', o.le w w' → ∀ ans, Ψ₁.post w' op cert ans → Typed o (Ψ₁.sum Ψ₂) w' Q (k ans)) := ⟨⟩
#obligation_proved inl_inv := @Effect4.Laws.Effects.Typed.inl_inv

theorem inr_inv {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {w : W} {op : T.Op}
    {k : (Signature.sum S T).Answer (.inr op) → Program (Signature.sum S T) A}
    (_h : Typed o (Ψ₁.sum Ψ₂) w Q (.vis (.inr op) k)) : ProofGraph.Obligation
    (∃ cert : Ψ₂.Cert op, Ψ₂.pre w op cert ∧
      ∀ w', o.le w w' → ∀ ans, Ψ₂.post w' op cert ans → Typed o (Ψ₁.sum Ψ₂) w' Q (k ans)) := ⟨⟩
#obligation_proved inr_inv := @Effect4.Laws.Effects.Typed.inr_inv

theorem pure_inv {o : WorldOrder W} {Ψ : Protocol W S} {Q : W → A → Prop} {w : W} {a : A}
    (_h : Typed o Ψ w Q (.pure a)) : ProofGraph.Obligation
    (Q w a) := ⟨⟩
#obligation_proved pure_inv := @Effect4.Laws.Effects.Typed.pure_inv
theorem plain_iff (o : WorldOrder W) (pre : W → S.Op → Prop)
    (post : W → (op : S.Op) → S.Answer op → Prop)
    (w : W) (Q : W → A → Prop) (p : Program S A) : ProofGraph.Obligation
    (Typed o (Protocol.plain pre post) w Q p ↔ PlainTyped o pre post w Q p) := ⟨⟩
#obligation_proved plain_iff := @Effect4.Laws.Effects.Typed.plain_iff

end Effect4.Laws.Effects.D12
#typed_state_obligations Effect4.Laws.Effects.D12 ceiling 0 using aesop (rule_sets := [Effect4.TypedState])
