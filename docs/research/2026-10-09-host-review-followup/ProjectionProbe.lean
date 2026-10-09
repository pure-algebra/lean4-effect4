import Effect4.Laws.Program.Agreement.Segment
import Effect4.Laws.Program.Agreement.Loop

namespace HostFollowupReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

private def root : NativeEff := .succeed (.lit .unit)
private def waiting : NFiber :=
  fiberOf (.async (.external (.external 0) .unit []) false none) []

-- The old run cannot cross this call within two steps.
#guard (localRun root 2 waiting Stores.empty).isNone
-- A nonempty reply tape can cross it within those same two steps.
#guard match localRunC [] root 2 waiting Stores.empty [.success .unit] with
  | some (.exit (.success .unit) _ []) => true
  | _ => false
-- Empty reply tape is the needed control for the proposed projection.
#guard match localRunC [] root 2 waiting Stores.empty [] with
  | some .waits => true
  | _ => false

private def loop : NativeEff :=
  .iterate none (.lit .unit) (.lit (.bool false)) (.lit .unit) (.lit .unit) root
#guard Looped loop
#guard !StraightRows [] loop

end HostFollowupReview
