import Effect4.Laws.Machine.RaceFirst
import Effect4.Machine.Alphabets

/-!
# First-exit race consumers and controls

The readers use the completion laws at the concrete machine's value and cause carrier.
The controls separate first-success selection from first-exit selection and omit the named proof bank.
-/

namespace Test.Machine.RaceFirst
open Effect4 Effect4.Machine Effect4.Supervision

/-- The named bank proves acceptance at the concrete machine carrier. -/
theorem accepts (s : RaceAllState Val Err Defect FiberId Ann) (child : FiberId)
    (exit : ExitV) (hlive : child ∈ s.live) (hopen : s.accepted = none) :
    (raceCompleteFirst s child exit).accepted = some exit := by
  aesop (rule_sets := [Effect4.Fibers])

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  s : RaceAllState Val Err Defect FiberId Ann
  child : FiberId
  exit : ExitV
  hlive : child ∈ s.live
  hopen : s.accepted = none
  ⊢ (raceCompleteFirst s child exit).accepted = some exit
-/
#guard_msgs (error) in
example (s : RaceAllState Val Err Defect FiberId Ann) (child : FiberId)
    (exit : ExitV) (hlive : child ∈ s.live) (hopen : s.accepted = none) :
    (raceCompleteFirst s child exit).accepted = some exit := by
  aesop

-- A first failure is accepted before a second live entrant finishes.
#guard (raceCompleteFirst
  { (RaceAllState.initial [⟨1⟩, ⟨2⟩] : RaceAllState Val Err Defect FiberId Ann) with
    live := [⟨1⟩, ⟨2⟩] }
  ⟨1⟩ (.failure (Cause.fail (.tagged "BadRequest" "bad")))).accepted =
    some (.failure (Cause.fail (.tagged "BadRequest" "bad")))

-- The same failure does not win a first-success race while another entrant is live.
#guard (raceComplete
  { (RaceAllState.initial [⟨1⟩, ⟨2⟩] : RaceAllState Val Err Defect FiberId Ann) with
    live := [⟨1⟩, ⟨2⟩] }
  ⟨1⟩ (.failure (Cause.fail (.tagged "BadRequest" "bad")))).accepted = none

end Test.Machine.RaceFirst
