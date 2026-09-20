def M1.StoresLaws.syncOpStep_memoComplete_some (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (exit : ExitV) {entry : MemoEntry} (_h : s.memo.entryAt memoMap layer = some entry) : ProofGraph.Obligation (syncOpStep (SyncOp.memoComplete layer memoMap exit) s =
      some ({ s with
          memo := s.memo.updateEntry memoMap layer id
          deferreds := (s.deferreds.complete entry.deferred (.ofExit exit)).1 },
        Val.unit)) := ⟨⟩

