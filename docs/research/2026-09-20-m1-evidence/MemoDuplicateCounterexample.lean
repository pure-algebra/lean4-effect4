import Effect4.Laws.Machine.Refinement

namespace Effect4.Machine.Refinement.MemoDuplicateCounterexample
open Effect4 Effect4.Machine

/-- Both old maps carry identity 0; only the first owns the entry. -/
def before : LegacyStores.Stores :=
  { LegacyStores.Stores.empty with
    deferreds := ⟨[⟨none, WakeList.empty⟩], []⟩
    memo := [⟨⟨0⟩, none, [([], ⟨1, Prim.success Val.unit, 0, ⟨0⟩,
      FinName.memoEntry [] ⟨0⟩⟩)]⟩, ⟨⟨0⟩, none, []⟩] }

def op : SyncOp := .memoComplete [] ⟨0⟩ (.success Val.unit)

def oldProjected := (LegacyStores.syncOpStep op before).map fun (s, a) => (alpha s, a)
/-- Rejected M1 candidate: the memoComplete arm omitted its historical memo-map write.
This is frozen so the counterexample remains reproducible after the runtime repair. -/
def rejectedOmittedUpdate (s : Stores) (layer : LayerId) (map : MemoMapId) (exit : ExitV) :
    Option (Stores × Val) :=
  match s.memo.entryAt map layer with
  | none => some (s, Val.unit)
  | some entry =>
      some ({ s with deferreds := (s.deferreds.complete entry.deferred (.ofExit exit)).1 }, Val.unit)

def newResult := rejectedOmittedUpdate (alpha before) [] ⟨0⟩ (.success Val.unit)

-- These projections isolate the lost behavior without changing any assertion.
#guard oldProjected.map (fun (s, _) => s.memo.map (fun m => m.entries.length)) = some [1, 1]
#guard newResult.map (fun (s, _) => s.memo.map (fun m => m.entries.length)) = some [1, 0]
#guard oldProjected ≠ newResult

-- The proposed identity update retains the former map normalization behavior.
#guard ((alpha before).memo.updateEntry ⟨0⟩ [] id).map (fun m => m.entries.length) = [1, 1]

namespace Wanted

def admitted : ProofGraph.Obligation (LegacyStores.StoresOk before) := ⟨⟩
#proof_wanted admitted

def mismatch : ProofGraph.Obligation (oldProjected ≠ newResult) := ⟨⟩
#proof_wanted mismatch

end Wanted

theorem admitted : LegacyStores.StoresOk before := by
  aesop (add norm unfold [LegacyStores.StoresOk, LegacyStores.DeferredOk,
    LegacyStores.Stores.ScopeKeysFresh, ScopeStore.KeysBelow, before, LegacyStores.Stores.empty])

theorem mismatch : oldProjected ≠ newResult := by decide

#print axioms admitted
#print axioms mismatch

end Effect4.Machine.Refinement.MemoDuplicateCounterexample
