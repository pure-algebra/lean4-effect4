import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Auto.Frames

namespace Effect4.Program.Typed
-- Isolate the changed record while producing all existing frame names exactly once.
#frame_rules RunFiberOk
#frame_rules RSavedOk BucketOk DispatcherOk CaptureOk ScopeOk ScopeEntryOk
  ScopeStoreOk MemoEntryOk MemoMapOk StoresOk RunMachineOk

-- A type annotation checks the generated API; no hand-written frame proof is installed.
#check (RunFiberOk.frame_origin :
  ∀ {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : Effect4.Program.Sched.RFiber), RunFiberOk P w e x →
    ∀ origin : Effect4.Machine.Origin, RunFiberOk P w e {x with origin := origin})

-- Keep the exact dependent id shape: all three clauses refer to the changed fiber id.
#check (RunFiberOk.frame_id :
  ∀ {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : Effect4.Program.Sched.RFiber), RunFiberOk P w e x →
    ∀ id : Effect4.FiberId,
      RSavedOk P w (.fiber id) x.frame →
      (∀ v, x.finalizing = some v → P.exit w (.fiber id) v) →
      (∀ v, x.exit = some v → P.exit w (.fiber id) v) →
      RunFiberOk P w e {x with id := id})
end Effect4.Program.Typed
