import Effect4.Laws.Run.Frame
import Effect4.Laws.Program.HeapSites.Core
import Effect4.Laws.Program.NativeHeapHistory
import Effect4.Laws.Auto.Obligations

/-!
# A cell predicate from a program's write sites

Placement: store-typing, R4. Proposed claim: cell-invariant-from-write-sites, role preservation.
Consumer: `Atomic.bounded`, through its proved write-site census.
Reach: the checked lexical source fragment, every control history, every compile budget.
The predicate describes each cell; it describes no relation between cells or fiber positions.
It establishes no progress or agreement with an outside runtime.
-/

set_option autoImplicit false

namespace Effect4.Program.HeapSites

open Effect4 Effect4.Machine Effect4.Program Effect4.Run



/-- Every reachable store row retains its source and environment level.
This theorem is the pointer of `cell-invariant-from-write-sites`.
The command/history induction belongs to `Machine.Lift`; the obligation is source provenance
and store preservation. Consumer: `Atomic.bounded`. -/
@[semantics "store-typing" (requirement := R4)]
theorem heap_sites_keep (b : Api.Built) (compileFuel : Nat) (P : Val → Prop)
    (fragment : SourceScope.Fragment b.program) (sites : SitesKeep b.program P) :
    ∀ m, ControlHistory b compileFuel m → HeapOk P m.state.refs := by
  intro m history
  exact SourceScope.heap_history_at b fragment compileFuel P sites m history

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
