import Effect4.Laws.Run.Frame
import Effect4.Laws.Program.SourceScope
import Effect4.Laws.Auto.Obligations

/-!
# A cell predicate from a program's write sites

Placement: store-typing, R4. Proposed claim: cell-invariant-from-write-sites, role soundness.
Consumer: `Atomic.bounded`, through its proved write-site census.
Reach: the native machine, every control history, every compile budget.
The predicate describes each cell; it describes no relation between cells or fiber positions.
It establishes no progress or agreement with an outside runtime.
-/

set_option autoImplicit false

namespace Effect4.Program.HeapSites

open Effect4 Effect4.Machine Effect4.Program Effect4.Run

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


/-- Every reachable store row must retain its source and environment level.
This planned goal is the pointer of `cell-invariant-from-write-sites`.
The command/history induction belongs to `Machine.Lift`; the obligation is source provenance
and store preservation. Consumer: `Atomic.bounded`. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal heap_sites_keep (b : Api.Built) (compileFuel : Nat) (P : Val → Prop)
    (sites : SitesKeep b.program P) :
    ∀ m, ControlHistory b compileFuel m → HeapOk P m.state.refs

/-- The `perform` sites of a program: each address of a `perform` node, its row, its request and
its level. -/
def performSites (root : NativeEff) : List (List Nat × NativeOp × Term × Option Nat) :=
  (Node.addresses (.eff root)).filterMap fun path =>
    match Node.at_ (.eff root) path with
    | some (.eff (.perform op request)) => some (path, op, request, levelAt (.eff root) 0 path)
    | _ => none

/-- **The site list is complete**: every `perform` node of a program is listed, with its level. -/
theorem performSites_complete {root : NativeEff} {path : List Nat} {op : NativeOp}
    {request : Term} (h : Node.at_ (.eff root) path = some (.eff (.perform op request))) :
    (path, op, request, levelAt (.eff root) 0 path) ∈ performSites root := by
  refine List.mem_filterMap.mpr ⟨path, (mem_addresses_iff (.eff root) path).mpr ?_, ?_⟩
  · rw [h]
    rfl
  · rw [h]

end Effect4.Program.HeapSites
