import Effects.Coalgebra.Protocol
import Effects.Algebra.Handler.Composition

/-!
# Typed programs and typed handlers

A protocol says which answers a host may give. A program then has a type under it: the values it
can end with when every answer it receives is admitted. `Program.Sat P Q p` says that `p`, answered
under `P`, ends only in values that satisfy `Q`. It is defined on the tree, by the program's own
recursion, so it is checked by structure, and it is sound for every host: a host that meets `P`
runs `p` only to values in `Q` (`Program.Sat.sound`).

A handler that implements each operation of `S` by a program over `T` is typed from `PS` to `PT`
(`Handler.Typed`) when each implementation, answered under `PT`, ends in an answer that `PS`
admits. Typed handlers are the deep modules of a stack: a host that meets `PT` behind a typed
handler meets `PS` (`Comodel.Meets.through`); a typed handler takes a program typed under `PS` to
a program typed under `PT` (`Program.Sat.interpret`); and typed handlers compose
(`Handler.Typed.through`). So a stack of layers, each checked against its two protocols, is
checked as a whole, and the host at its foot needs only to meet the last protocol.

Not claimed: the converse of soundness (a postcondition that every host meeting `P` gives is a
`Sat`); anything of a program that does not finish; protocols whose answers open operations.
-/

namespace Effects

universe uOp uAns uT uU

namespace Program

variable {S : Signature.{uOp, uAns}} {A B : Type uAns}

/-- **A program meets a postcondition under a protocol**: a finished program's value is in `Q`
after any answers that `P` admits. At an operation, every admitted answer must lead to a program
that meets it. -/
def Sat (P : Protocol S) (Q : A → Prop) : Program S A → Prop
  | .pure value => Q value
  | .vis operation next => ∀ answer, P operation answer → Sat P Q (next answer)

theorem sat_pure (P : Protocol S) (Q : A → Prop) (value : A) :
    Sat P Q (.pure value) ↔ Q value := Iff.rfl

theorem sat_vis (P : Protocol S) (Q : A → Prop) (operation : S.Op)
    (next : S.Answer operation → Program S A) :
    Sat P Q (.vis operation next) ↔ ∀ answer, P operation answer → Sat P Q (next answer) :=
  Iff.rfl

/-- A weaker postcondition is met too. -/
theorem Sat.mono {P : Protocol S} {Q Q' : A → Prop} (h : ∀ value, Q value → Q' value) :
    (program : Program S A) → Sat P Q program → Sat P Q' program
  | .pure value, hs => h value hs
  | .vis _ next, hs => fun answer ha => Sat.mono h (next answer) (hs answer ha)

/-- A stronger protocol admits fewer answers, so a program typed under the weaker one is typed
under it. -/
theorem Sat.weaken {P P' : Protocol S} {Q : A → Prop} (hle : P'.Le P) :
    (program : Program S A) → Sat P Q program → Sat P' Q program
  | .pure _, hs => hs
  | .vis operation next, hs => fun answer ha =>
    Sat.weaken hle (next answer) (hs answer (hle operation answer ha))

/-- One operation ends in an answer its protocol admits. -/
theorem Sat.perform (P : Protocol S) (operation : S.Op) :
    Sat P (P operation) (Program.perform operation) :=
  fun _ ha => ha

/-- **Sequencing**: a program typed into `R`, followed by a continuation typed from `R` into `Q`,
is typed into `Q`. -/
theorem Sat.bind {P : Protocol S} {R : A → Prop} {Q : B → Prop} (next : A → Program S B)
    (hnext : ∀ value, R value → Sat P Q (next value)) :
    (program : Program S A) → Sat P R program → Sat P Q (program.bind next)
  | .pure value, hs => hnext value hs
  | .vis _ rest, hs => fun answer ha => Sat.bind next hnext (rest answer) (hs answer ha)

/-- **Soundness**: a host that meets the protocol runs a typed program only to values in its
postcondition. -/
theorem Sat.sound {P : Protocol S} {Q : A → Prop} {σ : Type uAns} (host : Comodel S σ)
    (hmeets : host.Meets P) :
    (program : Program S A) → Sat P Q program →
      ∀ (state : σ) (value : A) (state' : σ), host.run program state = some (value, state') → Q value
  | .pure value, hs, state, value', state', hrun => by
    rw [Comodel.run_pure, Option.some.injEq, Prod.mk.injEq] at hrun
    rw [← hrun.1]
    exact hs
  | .vis operation next, hs, state, value, state', hrun => by
    rcases ha : host.answer operation state with _ | ⟨answer, state1⟩
    · rw [Comodel.run_vis_none host next ha] at hrun
      cases hrun
    · rw [Comodel.run_vis_some host next ha] at hrun
      exact Sat.sound host hmeets (next answer)
        (hs answer (hmeets operation state answer state1 ha)) state1 value state' hrun

end Program

namespace Handler

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}

/-- **A typed handler**: each operation's implementation, answered under `PT`, ends in an answer
that `PS` admits. -/
def Typed (PS : Protocol S) (PT : Protocol T) (impl : Handler S (Program T)) : Prop :=
  ∀ operation, Program.Sat PT (PS operation) (impl.handle operation)

/-- **A typed handler takes typed programs to typed programs**: translating a program typed under
`PS` by a handler typed from `PS` to `PT` gives a program typed under `PT`, into the same
postcondition. -/
theorem Typed.interpret {PS : Protocol S} {PT : Protocol T} {impl : Handler S (Program T)}
    (h : impl.Typed PS PT) {A : Type uAns} {Q : A → Prop} :
    (program : Program S A) → Program.Sat PS Q program →
      Program.Sat PT Q (Effects.interpret impl program)
  | .pure _, hs => hs
  | .vis operation next, hs =>
    Program.Sat.bind (fun answer => Effects.interpret impl (next answer))
      (fun answer ha => Typed.interpret h (next answer) (hs answer ha))
      (impl.handle operation) (h operation)

/-- **Typed handlers compose**: a layer typed from `PS` to `PT` over a layer typed from `PT` to
`PU` is typed from `PS` to `PU`. -/
theorem Typed.through {PS : Protocol S} {PT : Protocol T} {PU : Protocol U}
    {upper : Handler S (Program T)} {lower : Handler T (Program U)}
    (hupper : upper.Typed PS PT) (hlower : lower.Typed PT PU) :
    (upper.through lower).Typed PS PU :=
  fun operation => hlower.interpret (upper.handle operation) (hupper operation)

end Handler

namespace Comodel

variable {S : Signature.{uOp, uAns}} {T : Signature.{uT, uAns}} {σ : Type uAns}

/-- **A host behind a typed handler meets the upper protocol**: where the host meets `PT`, each
answer the implementation gives is one `PS` admits. -/
theorem Meets.through {PS : Protocol S} {PT : Protocol T} {impl : Handler S (Program T)}
    {host : Comodel T σ} (htyped : impl.Typed PS PT) (hmeets : host.Meets PT) :
    (host.through impl).Meets PS :=
  fun operation state answer state' ha =>
    Program.Sat.sound host hmeets (impl.handle operation) (htyped operation) state answer state' ha

end Comodel

end Effects
