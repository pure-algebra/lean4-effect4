import Effect4.Laws.Program.SourceScope

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep` and `Atomic.bounded`.
The cell predicate and source-site premise precede the execution preservation proof.
Their namespaces and statements remain unchanged.
-/
set_option autoImplicit false
namespace Effect4.Program.HeapSites
open Effect4 Effect4.Machine Effect4.Program

/-- A cell predicate holds at every cell of a heap. -/
def HeapOk (P : Val → Prop) (refs : RefHeap) : Prop := ∀ (i : Nat) (v : Val), refs[i]? = some v → P v

/-- **A store row keeps a cell predicate**: from a store whose every cell satisfies it, a step
leaves a store whose every cell satisfies it. It reads no key. -/
def OpKeeps (P : Val → Prop) (o : SyncOp) : Prop :=
  ∀ (s s' : Stores) (ans : Val), syncOpStep o s = some (s', ans) → HeapOk P s.refs →
    HeapOk P s'.refs

/-- **The level of an address**: the count of values in scope there, by the one binder table
(`Node.childLevel`, `Program/Binders.lean`), from level `n` at the node. `none` where the path
leaves the node. -/
abbrev levelAt := SourceScope.levelAt

/-- **The write sites of a root keep a cell predicate**: every store row that a `perform` node of
the root makes, at an environment of the node's level, keeps it. -/
def SitesKeep (root : NativeEff) (P : Val → Prop) : Prop :=
  ∀ (path : List Nat) (op : NativeOp) (request : Term) (env : List Val) (val : Val) (o : SyncOp),
    Node.at_ (.eff root) path = some (.eff (.perform op request)) →
    levelAt (.eff root) 0 path = some env.length →
    evalTerm env request = some val → NativeOp.syncOpOf op env val = some o → OpKeeps P o


end Effect4.Program.HeapSites
