import Effects.Algebra.Sum

/-!
# Laws.Effects.Protocol — a protocol-typed predicate on the free monad

Layer 0 of the typed-state invariant (`docs/research/2026-09-18-typed-state-composed-graph.md`
§4; probe Q1). Generic over the signature: an effect **protocol** says what an operation demands
of the **world** it is performed in (`pre`) and what its handler promises of the answer in the
world it answers in (`post`); a program is **typed** at a world for a result predicate when every
leaf satisfies the predicate at its world and every node's demand holds now and its
continuation is typed at every later world in which the handler answers within the protocol.

The continuation clause is quantified over later worlds, so weakening along the world order is
one `cases` and needs no induction on the tree; sequencing, widening of the result predicate
and the coproduct lift are one induction each. The tree's world is the typing tables and the
store; its protocols are the store's (`progress`'s hypotheses and conclusion) and the fiber
alphabet's (`OpOk`/`AnswerOk`). This module imports the pinned `Effects` algebra and nothing
of `Effect4`: it is a law of the free monad, kept here until the algebra takes it.
-/

set_option autoImplicit false

namespace Effect4.Laws.Effects

open _root_.Effects

universe u v w

/-- A world preorder: the tables and the store, ordered by extension. -/
structure WorldOrder (W : Type w) where
  le : W → W → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z

/-- An effect protocol with a ghost certificate chosen at each operation node.
The certificate lives only in the typing derivation, never in Program or stored Eff data. -/
structure Protocol (W : Type w) (S : Signature.{u, v}) where
  Cert : S.Op → Type v
  pre : W → (op : S.Op) → Cert op → Prop
  post : W → (op : S.Op) → Cert op → S.Answer op → Prop

variable {W : Type w} {S : Signature.{u, v}} {A : Type v}

/-- A program typed at world `w` for the result predicate `Q` under the protocol `Ψ`. -/
inductive Typed (o : WorldOrder W) (Ψ : Protocol W S) : W → (W → A → Prop) → Program S A → Prop
  | pure {w : W} {Q : W → A → Prop} {a : A} (h : Q w a) : Typed o Ψ w Q (.pure a)
  | vis {w : W} {Q : W → A → Prop} {op : S.Op} {k : S.Answer op → Program S A}
      (cert : Ψ.Cert op) (hpre : Ψ.pre w op cert)
      (hk : ∀ w', o.le w w' → ∀ ans, Ψ.post w' op cert ans → Typed o Ψ w' Q (k ans)) :
      Typed o Ψ w Q (.vis op k)

/-- Upward closure along the world order. -/
def Mono (o : WorldOrder W) (P : W → Prop) : Prop := ∀ {w w'}, o.le w w' → P w → P w'

/-- Weakening by construction: a demand and a result predicate that are upward closed make the
whole judgement upward closed, by one `cases`. -/
theorem Typed.mono {o : WorldOrder W} {Ψ : Protocol W S} {Q : W → A → Prop} {p : Program S A}
    (hpre : ∀ op cert, Mono o (fun w => Ψ.pre w op cert)) (hQ : ∀ a, Mono o (fun w => Q w a))
    {w w' : W} (hle : o.le w w') (h : Typed o Ψ w Q p) : Typed o Ψ w' Q p := by
  cases h with
  | pure h => exact .pure (hQ _ hle h)
  | vis cert hp hk =>
    exact .vis cert (hpre _ _ hle hp) (fun w'' hle' ans hpost => hk w'' (o.trans hle hle') ans hpost)

/-- Sequencing: the continuation is typed at whatever world the first program's leaf reaches. -/
theorem Typed.bind {o : WorldOrder W} {Ψ : Protocol W S} {B : Type v}
    {Q : W → A → Prop} {R : W → B → Prop} {p : Program S A} {k : A → Program S B} {w : W}
    (h : Typed o Ψ w Q p) (hk : ∀ w' a, Q w' a → Typed o Ψ w' R (k a)) :
    Typed o Ψ w R (p.bind k) := by
  induction h with
  | pure h => exact hk _ _ h
  | vis cert hp _ ih => exact .vis cert hp (fun w' hle ans hpost => ih w' hle ans hpost hk)

/-- Widening the result predicate. -/
theorem Typed.widen {o : WorldOrder W} {Ψ : Protocol W S} {Q Q' : W → A → Prop}
    {p : Program S A} {w : W} (h : Typed o Ψ w Q p) (hQ : ∀ w a, Q w a → Q' w a) :
    Typed o Ψ w Q' p := by
  induction h with
  | pure h => exact .pure (hQ _ _ h)
  | vis cert hp _ ih => exact .vis cert hp (fun w' hle ans hpost => ih w' hle ans hpost hQ)

/-- The protocol of a coproduct signature is the pair of protocols. -/
def Protocol.sum {T : Signature.{u, v}} (Ψ₁ : Protocol W S) (Ψ₂ : Protocol W T) :
    Protocol W (Signature.sum S T) where
  Cert op := match op with
    | .inl o => Ψ₁.Cert o
    | .inr o => Ψ₂.Cert o
  pre w op cert := match op, cert with
    | .inl o, cert => Ψ₁.pre w o cert
    | .inr o, cert => Ψ₂.pre w o cert
  post w op cert ans := match op, cert, ans with
    | .inl o, cert, ans => Ψ₁.post w o cert ans
    | .inr o, cert, ans => Ψ₂.post w o cert ans

/-- A program typed for the left protocol is typed for the sum once injected: the store half's
typing lifts to the scheduler's signature with no new arm. -/
theorem Typed.inl {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {p : Program S A} {w : W}
    (h : Typed o Ψ₁ w Q p) : Typed o (Ψ₁.sum Ψ₂) w Q p.inl := by
  induction h with
  | pure h => exact .pure h
  | vis cert hp _ ih =>
    exact .vis (Ψ := Ψ₁.sum Ψ₂) (op := .inl _) cert hp
      (fun w' hle ans hpost => ih w' hle ans hpost)

/-- Inversion at a left node: the store protocol's demand now, its promise at every later
world. -/
theorem Typed.inl_inv {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {w : W} {op : S.Op}
    {k : (Signature.sum S T).Answer (.inl op) → Program (Signature.sum S T) A}
    (h : Typed o (Ψ₁.sum Ψ₂) w Q (.vis (.inl op) k)) :
    ∃ cert : Ψ₁.Cert op, Ψ₁.pre w op cert ∧
      ∀ w', o.le w w' → ∀ ans, Ψ₁.post w' op cert ans → Typed o (Ψ₁.sum Ψ₂) w' Q (k ans) := by
  cases h with
  | vis cert hp hk => exact ⟨cert, hp, hk⟩

/-- Inversion at a right node: the fiber protocol's demand now, its promise at every later
world. This is what every operation arm of the step lemma starts from. -/
theorem Typed.inr_inv {o : WorldOrder W} {T : Signature.{u, v}} {Ψ₁ : Protocol W S}
    {Ψ₂ : Protocol W T} {Q : W → A → Prop} {w : W} {op : T.Op}
    {k : (Signature.sum S T).Answer (.inr op) → Program (Signature.sum S T) A}
    (h : Typed o (Ψ₁.sum Ψ₂) w Q (.vis (.inr op) k)) :
    ∃ cert : Ψ₂.Cert op, Ψ₂.pre w op cert ∧
      ∀ w', o.le w w' → ∀ ans, Ψ₂.post w' op cert ans → Typed o (Ψ₁.sum Ψ₂) w' Q (k ans) := by
  cases h with
  | vis cert hp hk => exact ⟨cert, hp, hk⟩

/-- Inversion at a leaf. -/
theorem Typed.pure_inv {o : WorldOrder W} {Ψ : Protocol W S} {Q : W → A → Prop} {w : W} {a : A}
    (h : Typed o Ψ w Q (.pure a)) : Q w a := by
  cases h with
  | pure h => exact h

/-- A unit certificate recovers a certificate-free pre/post contract. -/
def Protocol.plain (pre : W → S.Op → Prop)
    (post : W → (op : S.Op) → S.Answer op → Prop) : Protocol W S :=
  ⟨fun _ => PUnit, fun w op _ => pre w op, fun w op _ ans => post w op ans⟩

/-- The original certificate-free typing rules, retained only as the comparison judgment
for `Typed.plain_iff`. This is a predicate on the same Program, not another program carrier. -/
inductive PlainTyped (o : WorldOrder W) (pre : W → S.Op → Prop)
    (post : W → (op : S.Op) → S.Answer op → Prop) :
    W → (W → A → Prop) → Program S A → Prop
  | pure {w : W} {Q : W → A → Prop} {a : A} (h : Q w a) :
      PlainTyped o pre post w Q (.pure a)
  | vis {w : W} {Q : W → A → Prop} {op : S.Op} {k : S.Answer op → Program S A}
      (hpre : pre w op)
      (hk : ∀ w', o.le w w' → ∀ ans, post w' op ans → PlainTyped o pre post w' Q (k ans)) :
      PlainTyped o pre post w Q (.vis op k)

/-- For every world, result predicate and Program, unit certificates recover the old
certificate-free rules. Both directions preserve the same future-world quantification. -/
theorem Typed.plain_iff (o : WorldOrder W) (pre : W → S.Op → Prop)
    (post : W → (op : S.Op) → S.Answer op → Prop)
    (w : W) (Q : W → A → Prop) (p : Program S A) :
    Typed o (Protocol.plain pre post) w Q p ↔ PlainTyped o pre post w Q p := by
  constructor
  · intro h
    induction h with
    | pure h => exact .pure h
    | vis cert hp _ ih => exact .vis hp (fun w' hle ans hpost => ih w' hle ans hpost)
  · intro h
    induction h with
    | pure h => exact .pure h
    | vis hp _ ih => exact .vis PUnit.unit hp (fun w' hle ans hpost => ih w' hle ans hpost)

end Effect4.Laws.Effects
