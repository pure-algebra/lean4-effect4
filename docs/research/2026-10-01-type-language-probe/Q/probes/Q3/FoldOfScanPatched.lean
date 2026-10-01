import ProbeQ.Fold
import ProbeQ.FoldOf

/-! The same scan with the probe copy of `fold_of` (the `Prod` case added). -/

namespace ProbeQ
fold_of ProbeQ.Ty.members
fold_of ProbeQ.Ty.isNever
fold_of ProbeQ.Ty.isMember
fold_of ProbeQ.Ty.renderRaw
fold_of ProbeQ.Ty.closed
end ProbeQ
