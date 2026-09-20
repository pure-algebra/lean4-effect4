import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Auto.Frames

/-! Checked structural frame rules for every record in the generated state skeleton.
Each theorem retains explicit hypotheses for changed clauses. These are infrastructure
for preservation proofs, not proofs that arbitrary state writes preserve the invariant. -/
namespace Effect4.Program.Typed
/-- info: frame rules: 16 checked theorems, 87 reused clauses, 9 explicit premises -/
#guard_msgs in
#frame_rules RunFiberOk
/-- info: frame rules: 46 checked theorems, 90 reused clauses, 27 explicit premises -/
#guard_msgs in
#frame_rules RSavedOk BucketOk DispatcherOk CaptureOk ScopeOk ScopeEntryOk
  ScopeStoreOk MemoEntryOk MemoMapOk DeferredStoreOk StoresOk RunMachineOk
end Effect4.Program.Typed
