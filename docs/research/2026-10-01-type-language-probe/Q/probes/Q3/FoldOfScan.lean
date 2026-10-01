import ProbeQ.Fold
import Effect4.Program.FoldOf

/-! Scratch scan: which probe traversals `fold_of` accepts once `Ty` is nested. -/

namespace ProbeQ
fold_of ProbeQ.Ty.members
fold_of ProbeQ.Ty.isNever
fold_of ProbeQ.Ty.isMember
fold_of ProbeQ.Ty.renderRaw
fold_of ProbeQ.Ty.closed
end ProbeQ
