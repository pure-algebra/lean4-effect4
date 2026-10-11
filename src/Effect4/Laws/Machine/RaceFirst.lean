import Effect4.Machine.Supervision.FirstExit
import Effect4.Machine.Fibers
import Effect4.Laws.Auto.RuleSets
import Effect4.Laws.Auto.Semantics

/-!
# First-exit race laws

Concept: reactive-scheduling. Requirement: R4.
The completion and identity laws serve the timeout form's returned-outcome claim, R10.
The machine's actual exit observer consumes the completion worker.
The timeout observation consumes the retained selected child and full exit.
These laws establish selection stability, not progress or runtime agreement.
The source is rc.112 `internal/effect.ts`, `raceAllFirst`, at 1535 through 1580.
-/

set_option autoImplicit false
namespace Effect4.Supervision
universe u v
variable {β : Type v} {ε δ ι α : Type u}

/-- The existing first-success worker remains the exact specialization. -/
@[aesop norm simp (rule_sets := [Effect4.Fibers])]
theorem raceCompleteWith_firstSuccess (s : RaceAllState β ε δ ι α) (child : FiberId)
    (exit : Exit β ε δ ι α) :
    raceCompleteWith .firstSuccess s child exit = raceComplete s child exit := rfl

/-- An unknown child does not change first-exit bookkeeping. -/
theorem raceCompleteFirst_unknown (s : RaceAllState β ε δ ι α) (child : FiberId)
    (exit : Exit β ε δ ι α) (h : child ∉ s.live) :
    raceCompleteFirst s child exit = s := by
  simp only [raceCompleteFirst, if_neg h]

/-- First-exit selection keeps the complete exit, including arbitrary cause data. -/
@[aesop safe apply (rule_sets := [Effect4.Fibers]),
  semantics "reactive-scheduling" (requirement := R4)]
theorem raceCompleteFirst_accepts (s : RaceAllState β ε δ ι α) (child : FiberId)
    (exit : Exit β ε δ ι α) (hlive : child ∈ s.live) (hopen : s.accepted = none) :
    (raceCompleteFirst s child exit).accepted = some exit := by
  simp only [raceCompleteFirst, if_pos hlive, hopen]

/-- Once an exit is selected, later callbacks retain that exit. -/
@[aesop safe apply (rule_sets := [Effect4.Fibers]),
  semantics "reactive-scheduling" (requirement := R4)]
theorem raceCompleteFirst_keeps (s : RaceAllState β ε δ ι α) (child : FiberId)
    (exit accepted : Exit β ε δ ι α) (haccepted : s.accepted = some accepted) :
    (raceCompleteFirst s child exit).accepted = some accepted := by
  by_cases hlive : child ∈ s.live
  · simp only [raceCompleteFirst, if_pos hlive, haccepted]
    rw [raceComplete_after_accepted s child exit accepted hlive haccepted]
    exact haccepted
  · rw [raceCompleteFirst_unknown s child exit hlive]
    exact haccepted

/-- The consumer combines first acceptance with later cleanup callbacks. -/
theorem firstExit_retains (s : RaceAllState β ε δ ι α) (first later : FiberId)
    (exit other : Exit β ε δ ι α) (hlive : first ∈ s.live) (hopen : s.accepted = none) :
    (raceCompleteFirst (raceCompleteFirst s first exit) later other).accepted = some exit := by
  aesop (rule_sets := [Effect4.Fibers])

end Effect4.Supervision

namespace Effect4.Machine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable {κ : Type (max u v)}

/-- The new source action enters the existing registration mechanism in first-exit mode.
The source compilation and simulation action clauses consume this equation. -/
@[aesop norm simp (rule_sets := [Effect4.Fibers])]
theorem withFiber_raceAllFirst {χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (entrants : List (Prim ν σ β ε δ ι α)) (site : Option (List Nat) := none) :
    evaluatePrim.withFiber interp m f yielding (.raceAllFirst entrants site) =
      beginRace interp m f yielding entrants site .firstExit := rfl

/-- The legacy mode leaves selected-child data unchanged. -/
theorem Race.afterExit_firstSuccess (race : Race ν σ β ε δ ι α κ)
    (child : FiberId) (exit : Exit β ε δ ι α) (hmode : race.mode = .firstSuccess) :
    race.afterExit child exit = { race with state := Supervision.raceComplete race.state child exit } := by
  simp only [Race.afterExit, hmode, Supervision.raceCompleteWith]

/-- The actual first-exit observer records the selected entrant and full exit together. -/
@[semantics "reactive-scheduling" (requirement := R4)]
theorem Race.afterExit_first (race : Race ν σ β ε δ ι α κ) (child : FiberId)
    (exit : Exit β ε δ ι α) (hmode : race.mode = .firstExit)
    (hlive : child ∈ race.state.live) (hopen : race.state.accepted = none) :
    (race.afterExit child exit).selected = some child ∧
      (race.afterExit child exit).state.accepted = some exit := by
  have haccept := Supervision.raceCompleteFirst_accepts race.state child exit hlive hopen
  simp only [Race.afterExit, hmode, hopen, Supervision.raceCompleteWith, haccept]
  aesop

end Effect4.Machine
