import Effect4.Semantics.Logic

/-!
# Semantics.Equivalence

Owner: structural and semantic equivalence bridges.

Two checked flows are *denotationally equivalent* when they denote the same
program against every tape and input (`Flow.Equiv`). The denotation is
fuel-free (T2), so the relation mentions no fuel; and because the runner is
`interpret` of the denotation (T1), equivalent flows are indistinguishable by
every run — result, unconsumed tape and log, under every service, from every
log and state (`Equiv.runDefault`, `Equiv.runTape`) — and by every judgment of
the logic (`Equiv.wp`, `Equiv.wlp`, `Equiv.total`).

This is the relation the lowering theorems are instances of: the structured and
dispatch skeletons of one flow agreeing (packet D3, T4) is `Equiv` on the
programs they denote, and the trace-agreement gate (`docs/TRACE-DAG.md`,
`structured-agreement`) is `Equiv.runDefault` projected to the log.

Nothing here reaches the host. No `String` enters this module.
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val)

variable {Ty : Type} {alphabet : FlowAlphabet Ty}

/-- Denotational equivalence: the same program against every tape and input. -/
def Equiv (left right : CheckedFlow alphabet) : Prop :=
  ∀ (tape : Tape) (input : Val), denote left tape input = denote right tape input

namespace Equiv

theorem refl (flow : CheckedFlow alphabet) : Equiv flow flow := fun _ _ => rfl

theorem symm {left right : CheckedFlow alphabet} (h : Equiv left right) : Equiv right left :=
  fun tape input => (h tape input).symm

theorem trans {left middle right : CheckedFlow alphabet} (lm : Equiv left middle)
    (mr : Equiv middle right) : Equiv left right :=
  fun tape input => (lm tape input).trans (mr tape input)

/-- Equivalent flows interpret alike under every handler. -/
theorem interpret {M : Type → Type} [Monad M] {left right : CheckedFlow alphabet}
    (h : Equiv left right) (handler : Handler (FullSig alphabet) M) (tape : Tape) (input : Val) :
    Effects.interpret handler (denote left tape input) =
      Effects.interpret handler (denote right tape input) := by
  rw [h tape input]

/-- Equivalent flows run alike at any sufficient fuel: result, unconsumed tape
and log, under every service, from every log. -/
theorem runTape {M : Type → Type} [Monad M] [LawfulMonad M] {left right : CheckedFlow alphabet}
    (h : Equiv left right) (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (tape : Tape) (input : Val) (log : Effect4.Trace.Log) {fuelL fuelR : Nat}
    (enoughL : fuelFor left.erase tape ≤ fuelL) (enoughR : fuelFor right.erase tape ≤ fuelR) :
    (Flow.runTape fuelL left service nameOf tape input).run log =
      (Flow.runTape fuelR right service nameOf tape input).run log := by
  rw [runTape_eq_interpretRun_denote left service nameOf tape input log enoughL,
    runTape_eq_interpretRun_denote right service nameOf tape input log enoughR, h tape input]

/-- Equivalent flows run alike at their allotted fuel. -/
theorem runDefault {M : Type → Type} [Monad M] [LawfulMonad M] {left right : CheckedFlow alphabet}
    (h : Equiv left right) (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (Flow.runDefault left service nameOf tape input).run log =
      (Flow.runDefault right service nameOf tape input).run log := by
  rw [runDefault_eq_interpretRun_denote, runDefault_eq_interpretRun_denote, h tape input]

/-- Equivalent flows write the same log. -/
theorem log {σ : Type} {left right : CheckedFlow alphabet} (h : Equiv left right)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    (((Flow.runDefault left service nameOf tape input).run log).run s).1.2 =
      (((Flow.runDefault right service nameOf tape input).run log).run s).1.2 := by
  rw [h.runDefault service nameOf tape input log]

/-- Equivalent flows satisfy the same total judgments. -/
theorem wp {left right : CheckedFlow alphabet} (h : Equiv left right)
    (spec : Logic.Spec (FullSig alphabet)) (tape : Tape) (input : Val) (post : Val → Prop) :
    Flow.wp spec left tape input post ↔ Flow.wp spec right tape input post := by
  unfold Flow.wp
  rw [h tape input]

/-- Equivalent flows satisfy the same liberal judgments. -/
theorem wlp {left right : CheckedFlow alphabet} (h : Equiv left right)
    (spec : Logic.Spec (FullSig alphabet)) (tape : Tape) (input : Val) (post : Val → Prop) :
    Flow.wlp spec left tape input post ↔ Flow.wlp spec right tape input post := by
  unfold Flow.wlp
  rw [h tape input]

/-- Equivalent flows are total together. -/
theorem total {left right : CheckedFlow alphabet} (h : Equiv left right)
    (spec : Logic.Spec (FullSig alphabet)) (tape : Tape) (input : Val) :
    Flow.total spec left tape input ↔ Flow.total spec right tape input := by
  unfold Flow.total
  rw [h tape input]

end Equiv

/-- Equivalence is decided by the fuelled denotation at the allotted fuel: the
executable face of `Equiv`, which is what a receipt can compute. -/
theorem equiv_iff_denoteFuel (left right : CheckedFlow alphabet) :
    Equiv left right ↔
      ∀ (tape : Tape) (input : Val),
        denoteFuel (alphabet := alphabet) (fuelFor left.erase tape) left.erase left.erase.entry
            [input] tape =
          denoteFuel (alphabet := alphabet) (fuelFor right.erase tape) right.erase
            right.erase.entry [input] tape := by
  unfold Equiv
  constructor
  · intro h tape input
    rw [denoteFuel_eq_denote left tape input (Nat.le_refl _),
      denoteFuel_eq_denote right tape input (Nat.le_refl _)]
    exact h tape input
  · intro h tape input
    rw [← denoteFuel_eq_denote left tape input (Nat.le_refl _),
      ← denoteFuel_eq_denote right tape input (Nat.le_refl _)]
    exact h tape input

/-- A flow is equivalent to itself renamed: the denotation reads only the erased
graph, so two checked flows over the same raw flow are equivalent. -/
theorem equiv_of_erase_eq {left right : CheckedFlow alphabet} (same : left.erase = right.erase) :
    Equiv left right := by
  rw [equiv_iff_denoteFuel]
  intro tape input
  rw [same]

end Effect4.Flow
