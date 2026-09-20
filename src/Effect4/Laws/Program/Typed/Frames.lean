import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Auto.Frames

/-! Checked structural frame rules for every record in the generated state skeleton.
Each theorem retains explicit hypotheses for changed clauses. These are infrastructure
for preservation proofs, not proofs that arbitrary state writes preserve the invariant. -/
namespace Effect4.Program.Typed
#frame_rules RSavedOk BucketOk DispatcherOk RunFiberOk CaptureOk ScopeOk ScopeEntryOk
  ScopeStoreOk MemoEntryOk MemoMapOk StoresOk RunMachineOk
end Effect4.Program.Typed
