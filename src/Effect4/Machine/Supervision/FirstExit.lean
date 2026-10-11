module

public import Effect4.Machine.Supervision

/-!
# First-exit race completion

This module adds the data mode for the existing race mechanism.
`raceCompleteFirst` transcribes rc.112 `raceAllFirst`'s exit observer in
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:1549-1577`.
It retains the first live entrant's complete exit.
The existing race settlement path interrupts and awaits remaining entrants before publishing it.
The first-success worker and its statements stay unchanged.
The consumer is machine observer dispatch, then the timeout form's returned-outcome contract.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Supervision
universe u v

/-- A data selection rule for the existing machine race. -/
inductive RaceMode
  | firstSuccess
  | firstExit
  deriving DecidableEq, Repr

/-- First observed exit wins (`raceAllFirst`, rc.112 `internal/effect.ts:1549-1577`).
Later callbacks keep that exit through the existing cleanup bookkeeping. -/
def raceCompleteFirst {β : Type v} {ε δ ι α : Type u}
    (s : RaceAllState β ε δ ι α) (child : FiberId) (exit : Exit β ε δ ι α) :
    RaceAllState β ε δ ι α :=
  if child ∈ s.live then
    match s.accepted with
    | some _ => raceComplete s child exit
    | none =>
      let live := s.live.filter (fun id => decide (id ≠ child))
      { s with
        live := live
        remaining := s.remaining - 1
        winner := match exit with
          | .success value => some (child, value)
          | .failure _ => none
        accepted := some exit
        cleanupNeeded := !live.isEmpty
        requests := []
        cleanup := none
        cleanupRequested := false }
  else s

/-- The existing worker owns first success; the new worker owns first exit. -/
def raceCompleteWith {β : Type v} {ε δ ι α : Type u}
    (mode : RaceMode) (s : RaceAllState β ε δ ι α) (child : FiberId)
    (exit : Exit β ε δ ι α) : RaceAllState β ε δ ι α :=
  match mode with
  | .firstSuccess => raceComplete s child exit
  | .firstExit => raceCompleteFirst s child exit

end Effect4.Supervision
