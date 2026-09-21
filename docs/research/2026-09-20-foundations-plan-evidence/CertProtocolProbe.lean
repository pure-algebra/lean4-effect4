import Effects.Algebra.Sum
/-! Certificate-indexed protocol: does L0 survive a ghost certificate chosen at each node? -/
namespace CertProbe
open _root_.Effects
universe u v w
structure WorldOrder (W : Type w) where
  le : W → W → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z
structure Protocol (W : Type w) (S : Signature.{u, v}) where
  Cert : S.Op → Type v
  pre : W → (op : S.Op) → Cert op → Prop
  post : W → (op : S.Op) → Cert op → S.Answer op → Prop
variable {W : Type w} {S : Signature.{u, v}} {A : Type v}
inductive Typed (o : WorldOrder W) (Ψ : Protocol W S) : W → (W → A → Prop) → Program S A → Prop
  | pure {w : W} {Q : W → A → Prop} {a : A} (h : Q w a) : Typed o Ψ w Q (.pure a)
  | vis {w : W} {Q : W → A → Prop} {op : S.Op} {k : S.Answer op → Program S A}
      (cert : Ψ.Cert op) (hpre : Ψ.pre w op cert)
      (hk : ∀ w', o.le w w' → ∀ ans, Ψ.post w' op cert ans → Typed o Ψ w' Q (k ans)) :
      Typed o Ψ w Q (.vis op k)
def Mono (o : WorldOrder W) (P : W → Prop) : Prop := ∀ {w w'}, o.le w w' → P w → P w'
theorem Typed.mono {o : WorldOrder W} {Ψ : Protocol W S} {Q : W → A → Prop} {p : Program S A}
    (hpre : ∀ op cert, Mono o (fun w => Ψ.pre w op cert)) (hQ : ∀ a, Mono o (fun w => Q w a))
    {w w' : W} (hle : o.le w w') (h : Typed o Ψ w Q p) : Typed o Ψ w' Q p := by
  cases h with
  | pure h => exact .pure (hQ _ hle h)
  | vis cert hp hk =>
    exact .vis cert (hpre _ _ hle hp) (fun w'' hle' ans hpost => hk w'' (o.trans hle hle') ans hpost)
theorem Typed.bind {o : WorldOrder W} {Ψ : Protocol W S} {B : Type v}
    {Q : W → A → Prop} {R : W → B → Prop} {p : Program S A} {k : A → Program S B} {w : W}
    (h : Typed o Ψ w Q p) (hk : ∀ w' a, Q w' a → Typed o Ψ w' R (k a)) :
    Typed o Ψ w R (p.bind k) := by
  induction h with
  | pure h => exact hk _ _ h
  | vis cert hp _ ih => exact .vis cert hp (fun w' hle ans hpost => ih w' hle ans hpost hk)
theorem Typed.widen {o : WorldOrder W} {Ψ : Protocol W S} {Q Q' : W → A → Prop}
    {p : Program S A} {w : W} (h : Typed o Ψ w Q p) (hQ : ∀ w a, Q w a → Q' w a) :
    Typed o Ψ w Q' p := by
  induction h with
  | pure h => exact .pure (hQ _ _ h)
  | vis cert hp _ ih => exact .vis cert hp (fun w' hle ans hpost => ih w' hle ans hpost hQ)
def Protocol.sum {T : Signature.{u, v}} (Ψ₁ : Protocol W S) (Ψ₂ : Protocol W T) :
    Protocol W (Signature.sum S T) where
  Cert op := match op with
    | .inl o => Ψ₁.Cert o
    | .inr o => Ψ₂.Cert o
  pre w op c := match op, c with
    | .inl o, c => Ψ₁.pre w o c
    | .inr o, c => Ψ₂.pre w o c
  post w op c ans := match op, c, ans with
    | .inl o, c, ans => Ψ₁.post w o c ans
    | .inr o, c, ans => Ψ₂.post w o c ans
theorem Typed.inl {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {p : Program S A} {w : W}
    (h : Typed o Ψ₁ w Q p) : Typed o (Ψ₁.sum Ψ₂) w Q p.inl := by
  induction h with
  | pure h => exact .pure h
  | vis cert hp _ ih => exact .vis (Ψ := Ψ₁.sum Ψ₂) (op := .inl _) cert hp (fun w' hle ans hpost => ih w' hle ans hpost)
theorem Typed.inr_inv {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {w : W} {op : T.Op}
    {k : (Signature.sum S T).Answer (.inr op) → Program (Signature.sum S T) A}
    (h : Typed o (Ψ₁.sum Ψ₂) w Q (.vis (.inr op) k)) :
    ∃ cert : Ψ₂.Cert op, Ψ₂.pre w op cert ∧
      ∀ w', o.le w w' → ∀ ans, Ψ₂.post w' op cert ans → Typed o (Ψ₁.sum Ψ₂) w' Q (k ans) := by
  cases h with
  | vis cert hp hk => exact ⟨cert, hp, hk⟩
/-- The unit certificate recovers the landed protocol. -/
def Protocol.plain (pre : W → S.Op → Prop) (post : W → (op : S.Op) → S.Answer op → Prop) : Protocol W S :=
  ⟨fun _ => PUnit, fun w op _ => pre w op, fun w op _ ans => post w op ans⟩
#print axioms Typed.mono
#print axioms Typed.bind
#print axioms Typed.inl
#print axioms Typed.inr_inv
end CertProbe
