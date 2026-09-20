import Effect4.Machine.Stores
import Effect4.Laws.Auto.Obligations

namespace Effect4.Machine
open Effect4

def M1.StoresLaws.DeferredStore.complete_cells_length (self : DeferredStore) (cell : DeferredKey)
    (e : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation ((self.complete cell e).1.cells.length = self.cells.length) := ⟨⟩
#proof_wanted M1.StoresLaws.DeferredStore.complete_cells_length

def M1.StoresLaws.syncOpStep_deferredCompleteWith (s : Stores) (cell : DeferredKey)
    (c : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation (syncOpStep (SyncOp.deferredCompleteWith cell c) s =
      some ({ s with deferreds := (s.deferreds.complete cell c).1 },
        Val.bool (s.deferreds.complete cell c).2)) := ⟨⟩
#proof_wanted M1.StoresLaws.syncOpStep_deferredCompleteWith

def M1.StoresLaws.syncOpStep_deferredInterruptWith (s : Stores) (cell : DeferredKey)
    (interruptor : FiberId) : ProofGraph.Obligation (syncOpStep (SyncOp.deferredInterruptWith cell interruptor) s =
      some ({ s with deferreds :=
          (s.deferreds.complete cell
            (.ofExit (Exit.failure (Cause.interrupt (some interruptor))))).1 },
        Val.bool (s.deferreds.complete cell
          (.ofExit (Exit.failure (Cause.interrupt (some interruptor))))).2)) := ⟨⟩
#proof_wanted M1.StoresLaws.syncOpStep_deferredInterruptWith

def M1.StoresLaws.syncOpStep_memoBuild (s : Stores) (layer : LayerId) (memoMap : MemoMapId) : ProofGraph.Obligation (syncOpStep (SyncOp.memoBuild layer memoMap) s =
      some ({ s with
          scopes := s.scopes.make s.nextName FinalizerStrategy.sequential
          deferreds := s.deferreds.make.2
          memo := s.memo.insertEntry memoMap layer
            ⟨1, s.nextName, s.deferreds.make.1, FinName.memoEntry layer memoMap⟩
          nextName := s.nextName + 1 },
        Val.scopeHandle s.nextName)) := ⟨⟩
#proof_wanted M1.StoresLaws.syncOpStep_memoBuild

def M1.StoresLaws.syncOpStep_memoComplete_some (s : Stores) (layer : LayerId) (memoMap : MemoMapId)
    (exit : ExitV) {entry : MemoEntry} (_h : s.memo.entryAt memoMap layer = some entry) : ProofGraph.Obligation (syncOpStep (SyncOp.memoComplete layer memoMap exit) s =
      some ({ s with
          deferreds := (s.deferreds.complete entry.deferred (.ofExit exit)).1 },
        Val.unit)) := ⟨⟩
#proof_wanted M1.StoresLaws.syncOpStep_memoComplete_some

#typed_state_obligations Effect4.Machine.M1.StoresLaws ceiling 5 using aesop
end Effect4.Machine
