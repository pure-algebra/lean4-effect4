import Effect4.Laws.Machine.LegacyStores
import Effect4.Laws.Machine.Behaviour
import Effect4.Laws.Machine.CompletionData

/-!
M1's old-to-new representation projection, proposed in the observation packet §2.4 and §3.
The retained old step is independent of the new one. The decoder recognizes exactly the
three primitive heads emitted by the two Completion constructors. Its explicit invalid-code
fallback makes the projection total; the former stored-code invariant excludes that fallback.
-/

set_option autoImplicit false
namespace Effect4.Machine.Refinement
open Effect4 Effect4.Machine

/-- Read only the constructor image of completionPrim. -/
def readCompletion : Program → Option (Completion Val Err Defect FiberId Ann)
  | .success value => some (.ofExit (.success value))
  | .failure cause => some (.ofExit (.failure cause))
  | .sync (.op (.refGet cell)) => some (.ofRefGet cell)
  | _ => none

/-- Explicit totalization outside the old invariant; no fallback is reached on admitted code. -/
def invalidCompletionFallback : Completion Val Err Defect FiberId Ann := .ofExit (.success Val.unit)

def projectCompletion (p : Program) : Completion Val Err Defect FiberId Ann :=
  (readCompletion p).getD invalidCompletionFallback

def alphaCell (c : LegacyStores.DeferredCell) : DeferredCell :=
  ⟨c.completion.map projectCompletion, c.wake⟩

def alphaDeferred (d : LegacyStores.DeferredStore) : DeferredStore :=
  ⟨d.cells.map alphaCell, d.due.map (Owed.mapCode projectCompletion)⟩

def alphaMemoEntry (e : LegacyStores.MemoEntry) : MemoEntry :=
  ⟨e.observers, e.layerScope, e.deferred, e.finalizer⟩

def alphaMemoMap (m : LegacyStores.MemoMap) : MemoMap :=
  ⟨m.id, m.parent, m.entries.map fun (key, e) => (key, alphaMemoEntry e)⟩

def alphaMemo (w : LegacyStores.MemoWorld) : MemoWorld := w.map alphaMemoMap

def alpha (s : LegacyStores.Stores) : Stores :=
  ⟨s.refs, alphaDeferred s.deferreds, s.scopes, alphaMemo s.memo,
    s.timers, s.nextName, s.externals⟩

variable {ν σ χ κ φ η : Type}

/-- Change only the store parameter of the actual machine carrier. -/
def mapStores (f : LegacyStores.Stores → Stores)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ LegacyStores.Stores κ φ η) :
    RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η :=
  ⟨m.fibers, m.races, m.nextId, m.nextToken, m.nextRace, m.middlewareInstalled,
    m.armed, f m.state, m.trace, m.stuck⟩

/-- The same semantic observation fields on the retained old store carrier. -/
structure OldObs where
  exits : List (FiberId × Option ExitV)
  stores : LegacyStores.Stores

def obsOld (m : RunMachine ν σ Val Err Defect FiberId Ann χ LegacyStores.Stores κ φ η) : OldObs :=
  ⟨m.fibers.map fun f => (f.id, f.exit), m.state⟩

def projectObs (o : OldObs) : Obs := ⟨o.exits, alpha o.stores⟩

namespace Wanted

def read_write (c : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation
    (readCompletion (completionPrim c) = some c) := ⟨⟩
#proof_wanted read_write

def read_exact (p : Program) (c : Completion Val Err Defect FiberId Ann)
    (_h : readCompletion p = some c) : ProofGraph.Obligation (p = completionPrim c) := ⟨⟩
#proof_wanted read_exact

def syncOpStep_alpha (o : SyncOp) (s : LegacyStores.Stores) (_h : LegacyStores.StoresOk s) :
    ProofGraph.Obligation
      ((LegacyStores.syncOpStep o s).map (fun (s', a) => (alpha s', a)) =
        Effect4.Machine.syncOpStep o (alpha s)) := ⟨⟩
#proof_wanted syncOpStep_alpha

def obs_alpha (m : RunMachine ν σ Val Err Defect FiberId Ann χ LegacyStores.Stores κ φ η) :
    ProofGraph.Obligation (obs (mapStores alpha m) = projectObs (obsOld m)) := ⟨⟩
#proof_wanted obs_alpha


def syncOpStep_scopeKeysFresh {s s' : Stores} {o : SyncOp} {v : Val}
    (_hs : s.ScopeKeysFresh) (_h : Effect4.Machine.syncOpStep o s = some (s', v)) :
    ProofGraph.Obligation s'.ScopeKeysFresh := ⟨⟩
#proof_wanted syncOpStep_scopeKeysFresh

def project_write (c : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation
    (projectCompletion (completionPrim c) = c) := ⟨⟩
#proof_wanted project_write

def alphaDeferred_make (d : LegacyStores.DeferredStore) : ProofGraph.Obligation
    (((d.make).1, alphaDeferred (d.make).2) = (alphaDeferred d).make) := ⟨⟩
#proof_wanted alphaDeferred_make

def alphaDeferred_cellAt (d : LegacyStores.DeferredStore) (cell : DeferredKey) : ProofGraph.Obligation
    ((alphaDeferred d).cellAt cell = (d.cellAt cell).map alphaCell) := ⟨⟩
#proof_wanted alphaDeferred_cellAt

def alphaDeferred_setCell (d : LegacyStores.DeferredStore) (cell : DeferredKey) (c : LegacyStores.DeferredCell) : ProofGraph.Obligation
    (alphaDeferred (d.setCell cell c) = (alphaDeferred d).setCell cell (alphaCell c)) := ⟨⟩
#proof_wanted alphaDeferred_setCell

def alphaDeferred_isDone (d : LegacyStores.DeferredStore) (cell : DeferredKey) : ProofGraph.Obligation
    ((alphaDeferred d).isDone cell = d.isDone cell) := ⟨⟩
#proof_wanted alphaDeferred_isDone

def alphaDeferred_poll (d : LegacyStores.DeferredStore) (cell : DeferredKey) : ProofGraph.Obligation
    (((alphaDeferred d).poll cell).map Option.isSome = (d.poll cell).map Option.isSome) := ⟨⟩
#proof_wanted alphaDeferred_poll

def alphaDeferred_cancel (d : LegacyStores.DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    (alphaDeferred (d.cancel cell waiter token) = (alphaDeferred d).cancel cell waiter token) := ⟨⟩
#proof_wanted alphaDeferred_cancel

def alphaDeferred_complete (d : LegacyStores.DeferredStore) (cell : DeferredKey) (c : Completion Val Err Defect FiberId Ann) : ProofGraph.Obligation
    ((alphaDeferred (d.complete cell (completionPrim c)).1, (d.complete cell (completionPrim c)).2) = (alphaDeferred d).complete cell c) := ⟨⟩
#proof_wanted alphaDeferred_complete

def alphaMemo_mapAt (w : LegacyStores.MemoWorld) (map : MemoMapId) : ProofGraph.Obligation
    ((alphaMemo w).mapAt map = (w.mapAt map).map alphaMemoMap) := ⟨⟩
#proof_wanted alphaMemo_mapAt

def alphaMemo_setMap (w : LegacyStores.MemoWorld) (m : LegacyStores.MemoMap) : ProofGraph.Obligation
    (alphaMemo (w.setMap m) = (alphaMemo w).setMap (alphaMemoMap m)) := ⟨⟩
#proof_wanted alphaMemo_setMap

def alphaMemo_entryAt (w : LegacyStores.MemoWorld) (map : MemoMapId) (layer : LayerId) : ProofGraph.Obligation
    ((alphaMemo w).entryAt map layer = (w.entryAt map layer).map alphaMemoEntry) := ⟨⟩
#proof_wanted alphaMemo_entryAt

def alphaMemo_updateEntry (w : LegacyStores.MemoWorld) (map : MemoMapId) (layer : LayerId) (f : LegacyStores.MemoEntry → LegacyStores.MemoEntry) (g : MemoEntry → MemoEntry) (_h : ∀ e, alphaMemoEntry (f e) = g (alphaMemoEntry e)) : ProofGraph.Obligation
    (alphaMemo (w.updateEntry map layer f) = (alphaMemo w).updateEntry map layer g) := ⟨⟩
#proof_wanted alphaMemo_updateEntry

def alphaMemo_insertEntry (w : LegacyStores.MemoWorld) (map : MemoMapId) (layer : LayerId) (e : LegacyStores.MemoEntry) : ProofGraph.Obligation
    (alphaMemo (w.insertEntry map layer e) = (alphaMemo w).insertEntry map layer (alphaMemoEntry e)) := ⟨⟩
#proof_wanted alphaMemo_insertEntry

def alphaMemo_deleteEntry (w : LegacyStores.MemoWorld) (map : MemoMapId) (layer : LayerId) : ProofGraph.Obligation
    (alphaMemo (w.deleteEntry map layer) = (alphaMemo w).deleteEntry map layer) := ⟨⟩
#proof_wanted alphaMemo_deleteEntry

def alphaMemo_lookup (w : LegacyStores.MemoWorld) (layer : LayerId) (fuel : Nat) (map : MemoMapId) : ProofGraph.Obligation
    ((alphaMemo w).lookup layer fuel map = (w.lookup layer fuel map).map (fun (key, e) => (key, alphaMemoEntry e))) := ⟨⟩
#proof_wanted alphaMemo_lookup

def alphaMemo_get (w : LegacyStores.MemoWorld) (layer : LayerId) (map : MemoMapId) : ProofGraph.Obligation
    ((alphaMemo w).get layer map = (w.get layer map).map (fun (key, e) => (key, alphaMemoEntry e))) := ⟨⟩
#proof_wanted alphaMemo_get

def syncOpStep_alpha_total (o : SyncOp) (s : LegacyStores.Stores) : ProofGraph.Obligation
    ((LegacyStores.syncOpStep o s).map (fun (s', a) => (alpha s', a)) = Effect4.Machine.syncOpStep o (alpha s)) := ⟨⟩
#proof_wanted syncOpStep_alpha_total

def deferredOk_make (d : LegacyStores.DeferredStore) (_h : LegacyStores.DeferredOk d) : ProofGraph.Obligation
    (LegacyStores.DeferredOk d.make.2) := ⟨⟩
#proof_wanted deferredOk_make

def deferredOk_setCell (d : LegacyStores.DeferredStore) (key : DeferredKey) (c : LegacyStores.DeferredCell) (_h : LegacyStores.DeferredOk d) (_hc : ∀ p, c.completion = some p → LegacyStores.CompletionShaped p) : ProofGraph.Obligation
    (LegacyStores.DeferredOk (d.setCell key c)) := ⟨⟩
#proof_wanted deferredOk_setCell

def deferredOk_cancel (d : LegacyStores.DeferredStore) (key : DeferredKey) (waiter : FiberId) (token : Nat) (_h : LegacyStores.DeferredOk d) : ProofGraph.Obligation
    (LegacyStores.DeferredOk (d.cancel key waiter token)) := ⟨⟩
#proof_wanted deferredOk_cancel

def deferredOk_complete (d : LegacyStores.DeferredStore) (key : DeferredKey) (c : Completion Val Err Defect FiberId Ann) (_h : LegacyStores.DeferredOk d) : ProofGraph.Obligation
    (LegacyStores.DeferredOk (d.complete key (completionPrim c)).1) := ⟨⟩
#proof_wanted deferredOk_complete

def syncOpStep_deferredOk (o : SyncOp) (s s' : LegacyStores.Stores) (v : Val) (_hs : LegacyStores.DeferredOk s.deferreds) (_h : LegacyStores.syncOpStep o s = some (s', v)) : ProofGraph.Obligation
    (LegacyStores.DeferredOk s'.deferreds) := ⟨⟩
#proof_wanted syncOpStep_deferredOk

def syncOpStep_storesOk (o : SyncOp) (s s' : LegacyStores.Stores) (v : Val) (_hs : LegacyStores.StoresOk s) (_h : LegacyStores.syncOpStep o s = some (s', v)) : ProofGraph.Obligation
    (LegacyStores.StoresOk s') := ⟨⟩
#proof_wanted syncOpStep_storesOk

def memoBuild_cell_pending (s : Stores) (layer : LayerId) (map : MemoMapId) : ProofGraph.Obligation
    ((Effect4.Machine.syncOpStep (.memoBuild layer map) s).map (fun (s', _) => s'.deferreds.poll s.deferreds.make.1) = some (some none)) := ⟨⟩
#proof_wanted memoBuild_cell_pending

def memoComplete_cell_stored (s : Stores) (layer : LayerId) (map : MemoMapId) (exit : ExitV) (entry : MemoEntry) (cell : DeferredCell) (_he : s.memo.entryAt map layer = some entry) (_hc : s.deferreds.cellAt entry.deferred = some cell) (_hp : cell.completion = none) : ProofGraph.Obligation
    ((Effect4.Machine.syncOpStep (.memoComplete layer map exit) s).map (fun (s', _) => s'.deferreds.poll entry.deferred) = some (some (some (.ofExit exit)))) := ⟨⟩
#proof_wanted memoComplete_cell_stored

end Wanted

end Effect4.Machine.Refinement
