import Effects.Algebra.Sum

/-!
Probe Q1 (2026-09-18): a protocol-typed predicate on the free monad, generic over the
signature, with the continuation clause quantified over later worlds. Checks: weakening by
one `cases` (no induction on the tree), `bind`, `widen`, and the coproduct lift `inl`.
-/

set_option autoImplicit false

namespace Probe

open Effects

universe u v w

/-- A world preorder: the ghost tables and the store, ordered by extension. -/
structure WorldOrder (W : Type w) where
  le : W → W → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z

/-- An effect protocol over a signature at worlds `W`: what an operation demands of the world
it is performed in, and what its handler promises of the answer in the world it answers in. -/
structure Protocol (W : Type w) (S : Signature.{u, v}) where
  pre : W → S.Op → Prop
  post : W → (op : S.Op) → S.Answer op → Prop

variable {W : Type w} {S : Signature.{u, v}} {A : Type v}

/-- A program is typed at a world for a result predicate `Q` if every leaf satisfies `Q` at its
world and every node's demand holds now and its continuation is typed at every later world in
which the handler answers within the protocol. -/
inductive Typed (o : WorldOrder W) (Ψ : Protocol W S) : W → (W → A → Prop) → Program S A → Prop
  | pure {w : W} {Q : W → A → Prop} {a : A} (h : Q w a) : Typed o Ψ w Q (.pure a)
  | vis {w : W} {Q : W → A → Prop} {op : S.Op} {k : S.Answer op → Program S A}
      (hpre : Ψ.pre w op)
      (hk : ∀ w', o.le w w' → ∀ ans, Ψ.post w' op ans → Typed o Ψ w' Q (k ans)) :
      Typed o Ψ w Q (.vis op k)

/-- Upward closure, the one assumption a protocol's demands and a result predicate need. -/
def Mono (o : WorldOrder W) (P : W → Prop) : Prop := ∀ {w w'}, o.le w w' → P w → P w'

/-- Weakening by construction: one `cases`, no induction. -/
theorem Typed.mono {o : WorldOrder W} {Ψ : Protocol W S} {Q : W → A → Prop} {p : Program S A}
    (hpre : ∀ op, Mono o (fun w => Ψ.pre w op)) (hQ : ∀ a, Mono o (fun w => Q w a))
    {w w' : W} (hle : o.le w w') (h : Typed o Ψ w Q p) : Typed o Ψ w' Q p := by
  cases h with
  | pure h => exact .pure (hQ _ hle h)
  | vis hp hk => exact .vis (hpre _ hle hp) (fun w'' hle' ans hpost => hk w'' (o.trans hle hle') ans hpost)

/-- Sequencing, by induction on the derivation of the first program. -/
theorem Typed.bind {o : WorldOrder W} {Ψ : Protocol W S} {B : Type v}
    {Q : W → A → Prop} {R : W → B → Prop} {p : Program S A} {k : A → Program S B} {w : W}
    (h : Typed o Ψ w Q p) (hk : ∀ w' a, Q w' a → Typed o Ψ w' R (k a)) :
    Typed o Ψ w R (p.bind k) := by
  induction h with
  | pure h => exact hk _ _ h
  | vis hp _ ih => exact .vis hp (fun w' hle ans hpost => ih w' hle ans hpost hk)

theorem Typed.widen {o : WorldOrder W} {Ψ : Protocol W S} {Q Q' : W → A → Prop}
    {p : Program S A} {w : W} (h : Typed o Ψ w Q p) (hQ : ∀ w a, Q w a → Q' w a) :
    Typed o Ψ w Q' p := by
  induction h with
  | pure h => exact .pure (hQ _ _ h)
  | vis hp _ ih => exact .vis hp (fun w' hle ans hpost => ih w' hle ans hpost hQ)

/-- The protocol of a coproduct signature is the pair of protocols. -/
def Protocol.sum {T : Signature.{u, v}} (Ψ₁ : Protocol W S) (Ψ₂ : Protocol W T) :
    Protocol W (Signature.sum S T) where
  pre w op := match op with
    | .inl o => Ψ₁.pre w o
    | .inr o => Ψ₂.pre w o
  post w op ans := match op, ans with
    | .inl o, ans => Ψ₁.post w o ans
    | .inr o, ans => Ψ₂.post w o ans

/-- A program typed for the left protocol is typed for the sum once injected: the store
half's typing lifts to the scheduler's signature with no new arm. -/
theorem Typed.inl {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {p : Program S A} {w : W}
    (h : Typed o Ψ₁ w Q p) : Typed o (Ψ₁.sum Ψ₂) w Q p.inl := by
  induction h with
  | pure h => exact .pure h
  | vis hp _ ih => exact .vis hp (fun w' hle ans hpost => ih w' hle ans hpost)

/-- Inversion at a fiber-side node: the handler's promise is what the continuation may assume. -/
theorem Typed.inr_inv {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {w : W} {op : T.Op}
    {k : (Signature.sum S T).Answer (.inr op) → Program (Signature.sum S T) A}
    (h : Typed o (Ψ₁.sum Ψ₂) w Q (.vis (.inr op) k)) :
    Ψ₂.pre w op ∧ ∀ w', o.le w w' → ∀ ans, Ψ₂.post w' op ans → Typed o (Ψ₁.sum Ψ₂) w' Q (k ans) := by
  cases h with
  | vis hp hk => exact ⟨hp, hk⟩

end Probe

#print axioms Probe.Typed.mono
#print axioms Probe.Typed.bind
#print axioms Probe.Typed.inl
#print axioms Probe.Typed.inr_inv
