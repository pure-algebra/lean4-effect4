import Effects.Coalgebra.Sat

/-!
# Indexed signatures: protocols of a higher order

A first-order signature offers the same operations at every point of a run. A protocol of a
higher order changes what is offered as the run goes: an answer can open new operations. A
promise is the plain case: starting a job answers with a promise, and from then on the program
may await it, with the answer type that the promise recorded.

An indexed signature (`ISignature W`) has worlds `W`, the operations each world offers, their
answers, and the world after each answer. Its programs (`IProgram S A w`) start at a world and
end with a value whose type may depend on the world they end in (McBride's Kleisli arrows of
outrageous fortune, 2011; not filed here, so no statement of it is cited). Its hosts
(`IComodel`) answer the operations of each world from a state; a run returns the final world,
the value and the state. Its protocols (`IProtocol`) admit answers per world and operation, and
its typing (`IProgram.Sat`) is sound for every host that meets the protocol (`IProgram.Sat.sound`).

A first-order signature is the one-world case (`ISignature.const`). Programs, hosts and runs
embed exactly: `ofProgram` and `toProgram` are inverse (`toProgram_ofProgram`,
`ofProgram_toProgram`), and the embedded host runs the embedded program as the host runs the
program (`IComodel.run_ofProgram`).

Not claimed: indexed systems, bisimulations or handlers between indexed signatures; a promise's
fairness or progress; a host whose state is indexed by the world.
-/

namespace Effects

universe uW uOp uAns

set_option linter.checkUnivs false in
/-- **An indexed signature**: worlds; the operations each world offers; the answers to each; and
the world after each answer. Its universes occur together, as `Signature`'s do. -/
structure ISignature (W : Type uW) where
  Op : W → Type uOp
  Answer : (w : W) → Op w → Type uAns
  next : (w : W) → (operation : Op w) → Answer w operation → W

namespace ISignature

/-- A first-order signature as an indexed one with a single world. -/
def const (S : Signature.{uOp, uAns}) : ISignature.{0, uOp, uAns} Unit where
  Op _ := S.Op
  Answer _ operation := S.Answer operation
  next _ _ _ := ()

end ISignature

/-- **A program over an indexed signature**, from a world: it ends with a value of the type the
final world gives, or performs an operation that the world offers and continues, for every
answer, from the world after it. -/
inductive IProgram {W : Type uW} (S : ISignature.{uW, uOp, uAns} W) (A : W → Type uAns) :
    W → Type (max uW uOp uAns) where
  | pure {w : W} (value : A w) : IProgram S A w
  | vis {w : W} (operation : S.Op w)
      (next : (answer : S.Answer w operation) → IProgram S A (S.next w operation answer)) :
      IProgram S A w

namespace IProgram

variable {W : Type uW} {S : ISignature.{uW, uOp, uAns} W} {A B : W → Type uAns}

/-- Sequence: run the program, then the continuation from the world it ended in. -/
def bind : {w : W} → IProgram S A w → ((w' : W) → A w' → IProgram S B w') → IProgram S B w
  | _, .pure value, next => next _ value
  | _, .vis operation rest, next => .vis operation fun answer => (rest answer).bind next

/-- Perform one operation: its answer, at the world after it. -/
def perform {w : W} (operation : S.Op w) :
    IProgram S (fun w' => { answer : S.Answer w operation // S.next w operation answer = w' }) w :=
  .vis operation fun answer => .pure ⟨answer, rfl⟩

end IProgram

/-- **A host of an indexed signature**: at each world it answers an operation from its state, or
gives no answer. -/
structure IComodel {W : Type uW} (S : ISignature.{uW, uOp, uAns} W) (σ : Type uAns) where
  answer : (w : W) → (operation : S.Op w) → σ → Option (S.Answer w operation × σ)

namespace IComodel

variable {W : Type uW} {S : ISignature.{uW, uOp, uAns} W} {A : W → Type uAns} {σ : Type uAns}

/-- Run a program against a host: the final world, the value and the state, or no answer. -/
def run (host : IComodel S σ) : {w : W} → IProgram S A w → σ → Option ((w' : W) × A w' × σ)
  | w, .pure value, state => some ⟨w, value, state⟩
  | w, .vis operation next, state =>
    (host.answer w operation state).bind fun result => host.run (next result.1) result.2

theorem run_pure (host : IComodel S σ) {w : W} (value : A w) (state : σ) :
    host.run (.pure value) state = some ⟨w, value, state⟩ := rfl

theorem run_vis_none (host : IComodel S σ) {w : W} {operation : S.Op w}
    (next : (answer : S.Answer w operation) → IProgram S A (S.next w operation answer)) {state : σ}
    (h : host.answer w operation state = none) : host.run (.vis operation next) state = none := by
  show (host.answer w operation state).bind _ = none
  rw [h]
  rfl

theorem run_vis_some (host : IComodel S σ) {w : W} {operation : S.Op w}
    (next : (answer : S.Answer w operation) → IProgram S A (S.next w operation answer))
    {state state' : σ} {answer : S.Answer w operation}
    (h : host.answer w operation state = some (answer, state')) :
    host.run (.vis operation next) state = host.run (next answer) state' := by
  show (host.answer w operation state).bind _ = _
  rw [h]
  rfl

end IComodel

/-! ## The one-world case -/

namespace IProgram

variable {S : Signature.{uOp, uAns}} {A : Type uAns}

/-- A program as a program of the one-world signature. -/
def ofProgram : Program S A → IProgram (ISignature.const S) (fun _ => A) ()
  | .pure value => .pure value
  | .vis operation next => .vis operation fun answer => ofProgram (next answer)

/-- A program of the one-world signature as a program. -/
def toProgram : {w : Unit} → IProgram (ISignature.const S) (fun _ => A) w → Program S A
  | _, .pure value => .pure value
  | _, .vis operation next => .vis operation fun answer => toProgram (next answer)

theorem toProgram_ofProgram : (program : Program S A) → toProgram (ofProgram program) = program
  | .pure _ => rfl
  | .vis operation next => by
    show Program.vis operation (fun answer => toProgram (ofProgram (next answer))) = _
    congr 1
    funext answer
    exact toProgram_ofProgram (next answer)

theorem ofProgram_toProgram : {w : Unit} →
    (program : IProgram (ISignature.const S) (fun _ => A) w) → ofProgram (toProgram program) = program
  | _, .pure _ => rfl
  | _, .vis operation next => by
    show IProgram.vis operation (fun answer => ofProgram (toProgram (next answer))) = _
    congr 1
    funext answer
    exact ofProgram_toProgram (next answer)

end IProgram

namespace Comodel

variable {S : Signature.{uOp, uAns}} {σ : Type uAns}

/-- A host as a host of the one-world signature. -/
def toIndexed (host : Comodel S σ) : IComodel (ISignature.const S) σ where
  answer _ operation state := host.answer operation state

end Comodel

namespace IComodel

variable {S : Signature.{uOp, uAns}} {A : Type uAns} {σ : Type uAns}

/-- **The one-world embedding keeps runs**: the embedded host runs the embedded program as the host
runs the program. -/
theorem run_ofProgram (host : Comodel S σ) :
    (program : Program S A) → (state : σ) →
      host.toIndexed.run (IProgram.ofProgram program) state =
        (host.run program state).map fun result => ⟨(), result.1, result.2⟩
  | .pure _, _ => rfl
  | .vis operation next, state => by
    rcases h : host.answer operation state with _ | ⟨answer, state'⟩
    · have hi : host.toIndexed.answer () operation state = none := h
      rw [Comodel.run_vis_none host next h]
      exact IComodel.run_vis_none host.toIndexed _ hi
    · have hi : host.toIndexed.answer () operation state = some (answer, state') := h
      rw [Comodel.run_vis_some host next h]
      exact (IComodel.run_vis_some host.toIndexed _ hi).trans (run_ofProgram host (next answer) state')

end IComodel

/-! ## Protocols and typing -/

/-- **A protocol of an indexed signature**: at each world, the answers a host may give to each
operation. -/
abbrev IProtocol {W : Type uW} (S : ISignature.{uW, uOp, uAns} W) :=
  (w : W) → (operation : S.Op w) → S.Answer w operation → Prop

namespace IComodel

variable {W : Type uW} {S : ISignature.{uW, uOp, uAns} W} {σ : Type uAns}

/-- A host meets a protocol when every answer it gives, at every world, is admitted. -/
def Meets (host : IComodel S σ) (protocol : IProtocol S) : Prop :=
  ∀ w operation state answer state', host.answer w operation state = some (answer, state') →
    protocol w operation answer

end IComodel

namespace IProgram

variable {W : Type uW} {S : ISignature.{uW, uOp, uAns} W} {A B : W → Type uAns}

/-- **A program meets a postcondition under a protocol**: a finished program's world and value
satisfy `Q` after any answers that `P` admits. -/
def Sat (P : IProtocol S) (Q : (w : W) → A w → Prop) : {w : W} → IProgram S A w → Prop
  | w, .pure value => Q w value
  | w, .vis operation next => ∀ answer, P w operation answer → Sat P Q (next answer)

/-- Sequencing: a program typed into `R`, followed by a continuation typed from `R` into `Q`. -/
theorem Sat.bind {P : IProtocol S} {R : (w : W) → A w → Prop} {Q : (w : W) → B w → Prop}
    (next : (w : W) → A w → IProgram S B w) (hnext : ∀ w value, R w value → Sat P Q (next w value)) :
    {w : W} → (program : IProgram S A w) → Sat P R program → Sat P Q (program.bind next)
  | _, .pure value, hs => hnext _ value hs
  | _, .vis _ rest, hs => fun answer ha => Sat.bind next hnext (rest answer) (hs answer ha)

/-- **Soundness**: a host that meets the protocol runs a typed program only to worlds and values
in its postcondition. -/
theorem Sat.sound {P : IProtocol S} {Q : (w : W) → A w → Prop} {σ : Type uAns}
    (host : IComodel S σ) (hmeets : host.Meets P) :
    {w : W} → (program : IProgram S A w) → Sat P Q program →
      ∀ (state : σ) (w' : W) (value : A w') (state' : σ),
        host.run program state = some ⟨w', value, state'⟩ → Q w' value
  | _, .pure value, hs, state, w', value', state', hrun => by
    rw [IComodel.run_pure, Option.some.injEq] at hrun
    cases hrun
    exact hs
  | _, .vis operation next, hs, state, w', value, state', hrun => by
    rcases ha : host.answer _ operation state with _ | ⟨answer, state1⟩
    · rw [IComodel.run_vis_none host next ha] at hrun
      cases hrun
    · rw [IComodel.run_vis_some host next ha] at hrun
      exact Sat.sound host hmeets (next answer)
        (hs answer (hmeets _ operation state answer state1 ha)) state1 w' value state' hrun

end IProgram

end Effects
