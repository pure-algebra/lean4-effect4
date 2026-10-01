import Effect4.Laws.Machine.Behaviour
import Effect4.Laws.Api.Runner

/-!
# P3 — the decision tape acts on machines; the runner's behaviour is the final map

Formal pass, seat ALGEBRA, 2026-10-01. Two questions about behaviour as a function of the tape
(interaction trees, Xia et al. 2020; Moore and Mealy coalgebras, Jacobs ch. 2):

1. Does a tape act on machines as a monoid action, the machine-level K5, so that the meaning of a
   tape is the meaning of its prefix followed by its suffix (DB-03's "compatible finite
   prefixes")? The tree proves the action for the session journal (`replay_append`,
   `Laws/Api/Runner.lean:81`) but states nothing for `replayEval` over decisions. It holds, with
   fuel exhaustion absorbing: `replayEval_append` below.
2. `Laws/Api/Runner.lean:97-109` calls `behaviour` "the map into the final Mealy machine". The
   uniqueness half of finality (any map satisfying the unfolding equations is `behaviour`) is not
   stated. It holds: `behaviour_unique` below.
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P3

open Effect4 Effect4.Machine

universe u v

section Tape

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-- Continue a replay result with a suffix: a fuel frontier inside the prefix absorbs the suffix;
every other result hands its machine on. -/
def thenReplay (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (b : List (RunDecision ν σ β ε δ ι α)) :
    ReplayResult ν σ β ε δ ι α χ St κ φ η → ReplayResult ν σ β ε δ ι α χ St κ φ η
  | .frontier .fuel m => .frontier .fuel m
  | .frontier .tape m => replayEval interp fuel b m
  | .finished m => replayEval interp fuel b m
  | .stuck _ m => replayEval interp fuel b m

/-- A stuck machine stays stuck under any tape. -/
theorem replayEval_of_stuck (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) {why : Stuck} (hs : m.stuck = some why) :
    ∀ b : List (RunDecision ν σ β ε δ ι α), replayEval interp fuel b m = .stuck why m
  | [] => by simp only [replayEval, hs]
  | _ :: _ => by simp only [replayEval, hs]

/-- **The tape acts on machines.** Replaying `a ++ b` is replaying `a`, then `b` from the machine
`a` reached, unless the prefix ran out of fuel, which is absorbing. -/
theorem replayEval_append (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) :
    ∀ (a b : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      replayEval interp fuel (a ++ b) m = thenReplay interp fuel b (replayEval interp fuel a m)
  | [], b, m => by
    cases hs : m.stuck with
    | some why =>
      rw [List.nil_append, replayEval_of_stuck interp fuel m hs b]
      simp only [replayEval, hs, thenReplay]
      exact (replayEval_of_stuck interp fuel m hs b).symm
    | none =>
      rw [List.nil_append]
      by_cases hf : m.finished = true
      · simp only [replayEval, hs, hf, ↓reduceIte, thenReplay]
      · simp only [replayEval, hs, hf, Bool.false_eq_true, ↓reduceIte, thenReplay]
  | d :: a, b, m => by
    cases hs : m.stuck with
    | some why =>
      rw [List.cons_append]
      simp only [replayEval, hs, thenReplay]
      exact (replayEval_of_stuck interp fuel m hs b).symm
    | none =>
      rw [List.cons_append]
      by_cases hr : (stepDecisionState interp fuel m d).2 = true
      · simp only [replayEval, hs, hr, ↓reduceIte]
        exact replayEval_append interp fuel a b _
      · simp only [replayEval, hs, hr, Bool.false_eq_true, ↓reduceIte, thenReplay]

/-- Fuel exhaustion inside a prefix decides every extension of it. -/
theorem replayEval_append_fuel (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (a b : List (RunDecision ν σ β ε δ ι α)) (m m' : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (h : replayEval interp fuel a m = .frontier .fuel m') :
    replayEval interp fuel (a ++ b) m = .frontier .fuel m' := by
  rw [replayEval_append, h]
  rfl

/-- Off a fuel frontier, the suffix runs from the machine the prefix reached. -/
theorem replayEval_append_machine (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (a b : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (h : ∀ m', replayEval interp fuel a m ≠ .frontier .fuel m') :
    replayEval interp fuel (a ++ b) m =
      replayEval interp fuel b (replayEval interp fuel a m).machine := by
  rw [replayEval_append]
  cases hr : replayEval interp fuel a m with
  | frontier why m' =>
    cases why with
    | fuel => exact absurd hr (h m')
    | tape => rfl
  | finished m' => rfl
  | stuck why m' => rfl

end Tape

section Runner

open Effect4.Api.Runner

/-- **The uniqueness half of finality for the runner's Mealy machine.** Any map that satisfies
`behaviour`'s two unfolding equations (`behaviour_nil`, `behaviour_cons`) is `behaviour`: a
coalgebra morphism into the final Mealy machine is unique. -/
theorem behaviour_unique (h : Effect4.Api.Runner.Runner → List Command → List Api.HostSession.Phase)
    (hnil : ∀ p, h p [] = [])
    (hcons : ∀ p c rest, h p (c :: rest) = (step p c).2 :: h (step p c).1 rest) :
    ∀ (journal : List Command) (p : Effect4.Api.Runner.Runner), h p journal = behaviour p journal
  | [], p => by rw [hnil, behaviour_nil]
  | c :: rest, p => by rw [hcons, behaviour_cons, behaviour_unique h hnil hcons rest]

end Runner

end FormalPass.Algebra.P3

#print axioms FormalPass.Algebra.P3.replayEval_append
#print axioms FormalPass.Algebra.P3.replayEval_append_fuel
#print axioms FormalPass.Algebra.P3.replayEval_append_machine
#print axioms FormalPass.Algebra.P3.behaviour_unique
#print axioms FormalPass.Algebra.P3.replayEval_of_stuck
