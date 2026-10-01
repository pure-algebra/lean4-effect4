import Effect4.Program.Typed
import Test.Api.ExternalContract

/-! Verifier probe (fiberslice): P0 says path A "breaks no in-tree row (path probe: 15 rows)". The
path probe's list (`host-answers-evidence/PathProbes.lean:51-54`) is a hand list. Here its
`mentionsInternal` (copied verbatim, `PathProbes.lean:24-36`) is applied to the host table of
`Test/Api/ExternalContract.lean:15`, which the tree uses to test host-returned cell handles.
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false

namespace Research.Pass.FiberSliceVerify.PathA
open Effect4 Effect4.Program

/-- Copied from the path probe. -/
def mentionsInternal : Ty → Bool
  | .fiberOf _ _ => true
  | .refOf _ => true
  | .deferredOf _ _ => true
  | .handle target => internalHandleTargets.contains target
  | .option a => mentionsInternal a
  | .list a => mentionsInternal a
  | .causeOf a => mentionsInternal a
  | .prod a b => mentionsInternal a || mentionsInternal b
  | .except a b => mentionsInternal a || mentionsInternal b
  | .exitOf a b => mentionsInternal a || mentionsInternal b
  | .union a b => mentionsInternal a || mentionsInternal b
  | _ => false

def hostRowOk (row : Row) : Bool := !mentionsInternal row.answer && !mentionsInternal row.error

-- the tree's ExternalContract table has six host rows; path A refuses exactly the `cell` row,
-- whose answer is the internal cell spelling `Ref<number>`
#guard Test.Api.ExternalContract.table.length = 6
#guard Test.Api.ExternalContract.table.map hostRowOk = [true, false, true, true, true, true]
#guard (Test.Api.ExternalContract.table[1]?).map (·.answer) = some NativeOp.refTy
#guard (Test.Api.ExternalContract.table[1]?).map (·.registration) = some .external

end Research.Pass.FiberSliceVerify.PathA
