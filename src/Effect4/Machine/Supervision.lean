import Effect4.Machine.Fiber
import Effect4.Machine.Exit
/-!
# Fiber vocabulary shared with the reference machine

This module owns the fiber vocabulary the reference machine
`src/Effect4/Machine/Fibers.lean` uses: the mask mode, the fork options, the observer
mode, the scope mode, the frozen race bookkeeping `raceComplete`, and the
interrupt cause. The controller calculus this module used to hold was retired
on 2026-09-04 with `docs/research/2026-09-04-retire-old-machines.md`.
-/
set_option autoImplicit false
namespace Effect4.Supervision
universe u v w
inductive MaskMode | interruptible | uninterruptible | inherit
  deriving DecidableEq
structure ForkOptions where
  startImmediately : Bool
  daemon : Bool
  maskMode : MaskMode
  deriving DecidableEq
inductive ObserverMode | awaitValue | joinEffect
  deriving DecidableEq
inductive ScopeMode | forkIn | fiberRunIn
  deriving DecidableEq
structure WaitState (τ : Type u) where
  targets : List Effect4.FiberId
  published : List Effect4.FiberId
  result : τ
structure RaceAllState (β : Type v) (ε δ ι α : Type u) where
  unstarted : List Effect4.FiberId
  starting : Option Effect4.FiberId
  live : List Effect4.FiberId
  remaining : Nat
  failures : List (Effect4.Reason ε δ ι α)
  winner : Option (Effect4.FiberId × β)
  accepted : Option (Effect4.Exit β ε δ ι α)
  cleanupNeeded : Bool
  requests : List Effect4.FiberId
  cleanup : Option (WaitState (Effect4.Exit β ε δ ι α))
  cleanupRequested : Bool

variable {χ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- Outstanding actual publications, retaining target order. -/
def WaitState.pending {τ : Type u} (s : WaitState τ) : List FiberId :=
  s.targets.filter (fun child => decide (child ∉ s.published))

/-- Race bookkeeping before any entrant has started. -/
def RaceAllState.initial (entrants : List FiberId) : RaceAllState β ε δ ι α :=
  ⟨entrants, none, [], entrants.length, [], none, none, false, [], none, false⟩

/-- A callback preserves the first accepted result while updating live bookkeeping.
The winning callback records the empty/nonempty set branch at that moment. -/
def raceComplete (s : RaceAllState β ε δ ι α) (child : FiberId) (exit : Exit β ε δ ι α) :
    RaceAllState β ε δ ι α :=
  if child ∈ s.live then
    let live := s.live.filter (fun id => decide (id ≠ child))
    match s.accepted with
    | some _ => {s with live := live, remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait =>
          if child ∈ wait.pending then {wait with published := wait.published ++ [child]} else wait)}
    | none => match exit with
      | .success value => {s with live := live, remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !live.isEmpty, requests := [], cleanup := none, cleanupRequested := false}
      | .failure cause =>
        if s.remaining ≤ 1 then
          {s with live := live, remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false}
        else {s with live := live, remaining := s.remaining - 1, failures := s.failures ++ cause.reasons}
  else s

/-- Encode explicit interruptor data in the canonical annotated Cause. -/
def interruptCause (encode : FiberId → ι) (requester : Option FiberId)
    (annotations : ReasonAnnotations α) : Cause ε δ ι α :=
  Cause.annotate (Cause.interrupt (requester.map encode)) annotations false

/-! ## Frozen laws over the retained vocabulary -/

/-- MaskMode.cases_receipt at the frozen observation boundary.
census: fork.unsafe -/
theorem MaskMode.cases_receipt :
    forall mode : MaskMode, mode = .interruptible ∨ mode = .uninterruptible ∨ mode = .inherit := by
  intro mode
  cases mode <;> simp

/-- ObserverMode.cases_receipt at the frozen observation boundary.
census: fork.await fork.join -/
theorem ObserverMode.cases_receipt :
    forall mode : ObserverMode, mode = .awaitValue ∨ mode = .joinEffect := by
  intro mode
  cases mode <;> simp

/-- ScopeMode.cases_receipt at the frozen observation boundary.
census: fork.in fork.fiber-run-in -/
theorem ScopeMode.cases_receipt :
    forall mode : ScopeMode, mode = .forkIn ∨ mode = .fiberRunIn := by
  intro mode
  cases mode <;> simp

/-- interruptCause_eq at the frozen observation boundary.
census: fork.interrupt interrupt.accumulate -/
theorem interruptCause_eq :
    forall {ε δ ι α : Type u} (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α), (interruptCause encode requester annotations : Effect4.Cause ε δ ι α) = Effect4.Cause.annotate (Effect4.Cause.interrupt (requester.map encode)) annotations false := by
  intros
  rfl

/-- RaceAllState.initial_eq at the frozen observation boundary.
census: fork.race-all -/
theorem RaceAllState.initial_eq :
    forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (RaceAllState.initial entrants : RaceAllState β ε δ ι α) = {unstarted := entrants, starting := none, live := [], remaining := entrants.length, failures := [], winner := none, accepted := none, cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false} := by
  intros
  rfl

/-- raceComplete_unknown at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_unknown :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> raceComplete s child exit = s := by
  intros
  simp_all [raceComplete]

/-- raceComplete_after_accepted at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_after_accepted :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit accepted : Effect4.Exit β ε δ ι α), child ∈ s.live -> s.accepted = some accepted -> raceComplete s child exit = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait => if child ∈ WaitState.pending wait then {wait with published := wait.published ++ [child]} else wait)} := by
  intros
  simp_all [raceComplete]

/-- raceComplete_success at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_success :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (value : β), child ∈ s.live -> s.accepted = none -> raceComplete s child (.success value) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !(s.live.filter (fun id => decide (id ≠ child))).isEmpty, requests := [], cleanup := none, cleanupRequested := false} := by
  intros
  simp_all [raceComplete]

/-- raceComplete_failure_last at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_failure_last :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> s.remaining ≤ 1 -> raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false} := by
  intros
  simp_all [raceComplete]

/-- raceComplete_failure_pending at the frozen observation boundary.
census: fork.race-all -/
theorem raceComplete_failure_pending :
    forall {β : Type v} {ε δ ι α : Type u}, forall (s : RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> 1 < s.remaining -> raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons} := by
  intros
  simp_all [raceComplete]

end Effect4.Supervision
