import Effects.Coalgebra.Comodel

/-!
# Protocols of the first order

A protocol of a signature `S` says, for each operation, which answers a host may give. A host
meets a protocol when every answer it gives is admitted (`Comodel.Meets`). Reply admission is a
protocol: a consumer reads it off its types (an answer is admitted when it is a member of the
answer type at the call), and `Comodel.guard` turns a decidable protocol into a host that meets it.

Protocols combine as the hosts do: the sum of two protocols is met by the routed or shared host
(`Meets.route`, `Meets.share`), the pullback along a lens by the renamed host (`Meets.rename`).
The bottom protocol admits nothing, so a host that meets it never answers. Protocols are ordered
by weakening (`Protocol.Le`), and meeting is monotone in it.

A protocol of a higher order, where an answer opens new operations (a promise and its await), is
an indexed signature and is not in this module.
-/

namespace Effects

universe uOp uAns uT

/-- **A protocol of `S`**: for each operation, the answers a host may give. -/
abbrev Protocol (S : Signature.{uOp, uAns}) := (operation : S.Op) → S.Answer operation → Prop

namespace Protocol

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}}

/-- The protocol that admits no answer. -/
def bottom : Protocol S := fun _ _ => False

/-- The protocol that admits every answer. -/
def top : Protocol S := fun _ _ => True

/-- Each side of a sum under its own protocol. -/
def sum (left : Protocol S) (right : Protocol T) : Protocol (S ⊕ₛ T)
  | .inl operation => left operation
  | .inr operation => right operation

/-- The pullback of a protocol of `T` along a lens from `S`: an answer is admitted when it is the
pulled-back image of an answer admitted at the operation's image. -/
def pull (f : Signature.Hom S T) (protocol : Protocol T) : Protocol S :=
  fun operation answer => ∃ answer', protocol (f.op operation) answer' ∧ f.back operation answer' = answer

/-- Weakening: `P` admits no more than `Q`. -/
def Le (P Q : Protocol S) : Prop := ∀ operation answer, P operation answer → Q operation answer

theorem Le.refl (P : Protocol S) : P.Le P := fun _ _ h => h

theorem Le.trans {P Q R : Protocol S} (h : P.Le Q) (h' : Q.Le R) : P.Le R :=
  fun operation answer hp => h' operation answer (h operation answer hp)

theorem bottom_le (P : Protocol S) : (bottom : Protocol S).Le P := fun _ _ h => h.elim

theorem le_top (P : Protocol S) : P.Le top := fun _ _ _ => trivial

end Protocol

namespace Comodel

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}} {σ τ : Type uAns}

/-- **A host meets a protocol** when every answer it gives is admitted. -/
def Meets (host : Comodel S σ) (protocol : Protocol S) : Prop :=
  ∀ operation state answer state', host.answer operation state = some (answer, state') →
    protocol operation answer

theorem Meets.mono {host : Comodel S σ} {P Q : Protocol S} (h : host.Meets P) (hle : P.Le Q) :
    host.Meets Q :=
  fun operation state answer state' ha => hle operation answer (h operation state answer state' ha)

/-- A host that meets the bottom protocol never answers. -/
theorem Meets.bottom {host : Comodel S σ} (h : host.Meets Protocol.bottom) (operation : S.Op)
    (state : σ) : host.answer operation state = none := by
  rcases ha : host.answer operation state with _ | ⟨answer, state'⟩
  · rfl
  · exact (h operation state answer state' ha).elim

/-- The guarded host meets the protocol its test decides. -/
theorem guard_meets (admit : (operation : S.Op) → S.Answer operation → Bool) (host : Comodel S σ) :
    (host.guard admit).Meets (fun operation answer => admit operation answer = true) := by
  intro operation state answer state' ha
  simp only [guard, Option.filter_eq_some_iff] at ha
  exact ha.2

/-- Guarding a host that already meets the test changes nothing. -/
theorem guard_of_meets {admit : (operation : S.Op) → S.Answer operation → Bool} {host : Comodel S σ}
    (h : host.Meets (fun operation answer => admit operation answer = true)) :
    host.guard admit = host := by
  cases host with
  | mk answer =>
    show Comodel.mk (fun operation state =>
      (answer operation state).filter fun result => admit operation result.1) = Comodel.mk answer
    congr 1
    funext operation state
    rcases ha : answer operation state with _ | ⟨reply, state'⟩
    · rfl
    · simp only [Option.filter_some, h operation state reply state' ha, ↓reduceIte]

theorem Meets.route {left : Comodel S σ} {right : Comodel T τ} {P : Protocol S} {Q : Protocol T}
    (hl : left.Meets P) (hr : right.Meets Q) : (left.route right).Meets (P.sum Q) := by
  intro operation state answer state' ha
  cases operation with
  | inl operation =>
    rcases h : left.answer operation state.1 with _ | ⟨reply, state1⟩
    · have e : (left.route right).answer (.inl operation) state = none := by
        show (left.answer operation state.1).map _ = none
        rw [h]
        rfl
      rw [e] at ha
      cases ha
    · have e : (left.route right).answer (.inl operation) state =
          some (reply, (state1, state.2)) := by
        show (left.answer operation state.1).map _ = _
        rw [h]
        rfl
      rw [e] at ha
      have hreply : reply = answer := congrArg Prod.fst (Option.some.inj ha)
      show P operation answer
      rw [← hreply]
      exact hl operation state.1 reply state1 h
  | inr operation =>
    rcases h : right.answer operation state.2 with _ | ⟨reply, state1⟩
    · have e : (left.route right).answer (.inr operation) state = none := by
        show (right.answer operation state.2).map _ = none
        rw [h]
        rfl
      rw [e] at ha
      cases ha
    · have e : (left.route right).answer (.inr operation) state =
          some (reply, (state.1, state1)) := by
        show (right.answer operation state.2).map _ = _
        rw [h]
        rfl
      rw [e] at ha
      have hreply : reply = answer := congrArg Prod.fst (Option.some.inj ha)
      show Q operation answer
      rw [← hreply]
      exact hr operation state.2 reply state1 h

theorem Meets.share {left : Comodel S σ} {right : Comodel T σ} {P : Protocol S} {Q : Protocol T}
    (hl : left.Meets P) (hr : right.Meets Q) : (left.share right).Meets (P.sum Q) := by
  intro operation state answer state' ha
  cases operation with
  | inl operation => exact hl operation state answer state' ha
  | inr operation => exact hr operation state answer state' ha

theorem Meets.rename {host : Comodel T σ} {Q : Protocol T} (h : host.Meets Q)
    (f : Signature.Hom S T) : (host.rename f).Meets (Q.pull f) := by
  intro operation state answer state' ha
  rcases hh : host.answer (f.op operation) state with _ | ⟨reply, state1⟩
  · have e : (host.rename f).answer operation state = none := by
      show (host.answer (f.op operation) state).map _ = none
      rw [hh]
      rfl
    rw [e] at ha
    cases ha
  · have e : (host.rename f).answer operation state = some (f.back operation reply, state1) := by
      show (host.answer (f.op operation) state).map _ = _
      rw [hh]
      rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at ha
    exact ⟨reply, h (f.op operation) state reply state1 hh, ha.1⟩

/-- The reply host meets a protocol when every reply decodes to an admitted answer. -/
theorem Meets.replies {R : Type uAns} {decode : (operation : S.Op) → R → Option (S.Answer operation)}
    {P : Protocol S} (h : ∀ operation reply answer, decode operation reply = some answer →
      P operation answer) : (Comodel.replies decode).Meets P := by
  intro operation state answer state' ha
  cases state with
  | nil => cases ha
  | cons reply rest =>
    rcases hd : decode operation reply with _ | decoded
    · have e : (Comodel.replies decode).answer operation (reply :: rest) = none := by
        show (decode operation reply).map _ = none
        rw [hd]
        rfl
      rw [e] at ha
      cases ha
    · have e : (Comodel.replies decode).answer operation (reply :: rest) = some (decoded, rest) := by
        show (decode operation reply).map _ = _
        rw [hd]
        rfl
      rw [e, Option.some.injEq, Prod.mk.injEq] at ha
      rw [← ha.1]
      exact h operation reply decoded hd

/-- Recording keeps a host's protocol. -/
theorem Meets.record {R : Type uAns} {encode : (operation : S.Op) → S.Answer operation → R}
    {host : Comodel S σ} {P : Protocol S} (h : host.Meets P) : (host.record encode).Meets P := by
  intro operation state answer state' ha
  rcases hh : host.answer operation state.1 with _ | ⟨reply, state1⟩
  · have e : (host.record encode).answer operation state = none := by
      show (host.answer operation state.1).map _ = none
      rw [hh]
      rfl
    rw [e] at ha
    cases ha
  · have e : (host.record encode).answer operation state =
        some (reply, (state1, state.2 ++ [encode operation reply])) := by
      show (host.answer operation state.1).map _ = _
      rw [hh]
      rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at ha
    rw [← ha.1]
    exact h operation state.1 reply state1 hh

end Comodel

end Effects
