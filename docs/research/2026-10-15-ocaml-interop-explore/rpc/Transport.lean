import Effects.Coalgebra

/-!
# A transport, modeled: a probe

Exploration probe (2026-10-15), over the `effects` package's hosts (`Effects.Comodel`). Not part
of any library root; run with `lake env lean` on this file.

A request/response channel is a signature with one operation, `exchange`, that sends a message
and answers a message (`Wire`). A codec writes a signature's operations and answers as messages.
The client implements each operation by one exchange (`client`); the server answers exchanges
from any host of the signature (`serve`). The law: when the codec reads back what it writes,
the client run through the server is the host itself (`through_serve`). Stacking transports is
then free (`through_serve_stacked`): rows over messages over frames is two applications.

What this does not model: a channel that carries several calls at once (correlation by id), an
interrupt, a lost or duplicated message, or the cost of a call. Those need a channel with state
and a named observation.
-/

namespace Explore.Transport

open Effects

/-- The wire of a request/response channel. `some m` sends `m` and answers a message; `none` is
the refusal, an operation with no answer, which a client performs when a reply does not decode. -/
def Wire (Msg : Type) : Signature.{0, 0} where
  Op := Option Msg
  Answer
    | some _ => Msg
    | none => Empty

/-- A codec of a signature into messages. -/
structure Codec (S : Signature.{0, 0}) (Msg : Type) where
  encReq : S.Op → Msg
  decReq : Msg → Option S.Op
  encAns : (op : S.Op) → S.Answer op → Msg
  decAns : (op : S.Op) → Msg → Option (S.Answer op)

/-- The two read-backs the law needs. -/
structure Codec.Lawful {S : Signature.{0, 0}} {Msg : Type} (c : Codec S Msg) : Prop where
  req : ∀ op, c.decReq (c.encReq op) = some op
  ans : ∀ op a, c.decAns op (c.encAns op a) = some a

variable {S : Signature.{0, 0}} {Msg : Type} {σ : Type}

/-- The client: each operation is one exchange of its encoded request; the reply is decoded at
the operation, and a reply that does not decode is the refusal. -/
def client (c : Codec S Msg) : Handler S (Program (Wire Msg)) where
  handle op := .vis (some (c.encReq op)) fun reply =>
    match c.decAns op reply with
    | some a => .pure a
    | none => .vis none fun e => Empty.elim e

/-- The server: an exchange decodes its request, asks the host, and encodes the answer. The
refusal is never answered. -/
def serve (c : Codec S Msg) (host : Comodel S σ) : Comodel (Wire Msg) σ where
  answer
    | some m => fun st =>
      (c.decReq m).bind fun op => (host.answer op st).map fun r => (c.encAns op r.1, r.2)
    | none => fun _ => none

/-- Two hosts that answer alike are one. -/
theorem comodel_ext {T : Signature.{0, 0}} {a b : Comodel T σ}
    (h : ∀ op st, a.answer op st = b.answer op st) : a = b := by
  cases a
  cases b
  congr 1
  funext op st
  exact h op st

/-- **The transport law.** Through a lawful codec, the client run against the server is the host. -/
theorem through_serve (c : Codec S Msg) (hc : c.Lawful) (host : Comodel S σ) :
    Comodel.through (client c) (serve c host) = host := by
  apply comodel_ext
  intro op st
  show (serve c host).run ((client c).handle op) st = host.answer op st
  rcases h : host.answer op st with _ | ⟨a, st'⟩
  · apply Comodel.run_vis_none
    show (c.decReq (c.encReq op)).bind _ = none
    rw [hc.req op]
    show (host.answer op st).map _ = none
    rw [h]
    rfl
  · have hs : (serve c host).answer (some (c.encReq op)) st = some (c.encAns op a, st') := by
      show (c.decReq (c.encReq op)).bind _ = _
      rw [hc.req op]
      show (host.answer op st).map _ = _
      rw [h]
      rfl
    rw [show (client c).handle op = .vis (some (c.encReq op)) (fun reply =>
        match c.decAns op reply with
        | some a => .pure a
        | none => .vis none fun e => Empty.elim e) from rfl,
      Comodel.run_vis_some (serve c host) _ hs]
    show (serve c host).run (match c.decAns op (c.encAns op a) with
      | some a => .pure a
      | none => .vis none fun e => Empty.elim e) st' = some (a, st')
    rw [hc.ans op a]
    rfl

/-- **Stacking is free.** A transport for the rows over messages, and one for those messages over
frames: the stack gives the host back. -/
theorem through_serve_stacked {M₁ M₂ : Type} (c₁ : Codec S M₁) (c₂ : Codec (Wire M₁) M₂)
    (h₁ : c₁.Lawful) (h₂ : c₂.Lawful) (host : Comodel S σ) :
    Comodel.through (client c₁) (Comodel.through (client c₂) (serve c₂ (serve c₁ host))) = host := by
  rw [through_serve c₂ h₂, through_serve c₁ h₁]

/-! ## A finite instance: a counter host, its messages as lists of numbers

Each line below is a finite evaluation or a control. -/

/-- A counter: `add n` adds `n` and answers the new total. -/
abbrev Counter : Signature.{0, 0} := ⟨Nat, fun _ => Nat⟩

def counter : Comodel Counter Nat where
  answer n st := some (st + n, st + n)

/-- The messages: a request is `[0, n]`, an answer `[1, total]`. -/
def listCodec : Codec Counter (List Nat) where
  encReq n := [0, n]
  decReq | [0, n] => some n | _ => none
  encAns _ total := [1, total]
  decAns _ | [1, total] => some total | _ => none

theorem listCodec_lawful : listCodec.Lawful := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- A codec that reads every answer as zero: it is not lawful. -/
def lossyCodec : Codec Counter (List Nat) := { listCodec with decAns := fun _ _ => some 0 }

-- finite evaluation: through the transport, `add 5` from 10 answers 15, as the host does
#guard (Comodel.through (client listCodec) (serve listCodec counter)).answer 5 10 = some (15, 15)
-- control: the lossy codec changes the answer, so `Codec.Lawful` is the premise that matters
#guard (Comodel.through (client lossyCodec) (serve lossyCodec counter)).answer 5 10 = some (0, 15)

end Explore.Transport
