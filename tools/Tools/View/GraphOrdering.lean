import Tools.View.Picture

/-! Stable graph ordering, with each barycentre stored before comparison.
Placement: `docs/research/2026-10-13-graph-ordering-plan.md`.
The observation is the exact sorted key list, without a crossing claim. -/

namespace Tools.View.Graph

/-- The position of a key in a rank's order. -/
def posIn (order : List Key) (k : Key) : Nat := order.findIdx (· == k)

/-- An item's barycentre as a fraction; no neighbours means its current position. -/
def barycentre (order beside : List Key) (neighbours : Key → List Key) (k : Key) : Nat × Nat :=
  let ns := (neighbours k).filter beside.contains
  if ns.isEmpty then (2 * posIn order k, 2)
  else (ns.foldl (fun s n => s + 2 * posIn beside n) 0, 2 * ns.length)

/-- Compare barycentre fractions by their cross products. -/
def barycentreLE (a b : Nat × Nat) : Bool := a.1 * b.2 ≤ b.1 * a.2

/-- Order one rank by its neighbours' barycentres, computed once per item.
The stable sort retains ties and the current position of an item without neighbours. -/
def reorder (order beside : List Key) (neighbours : Key → List Key) : List Key :=
  ((order.map fun k => (k, barycentre order beside neighbours k)).mergeSort
    fun a b => barycentreLE a.2 b.2).map (·.1)

/-- The stored scores give the original key order, including duplicate keys and ties.
`Graph.orders` consumes this tool law for R14 under decisions row 334 (3).
Placement: concept `initial-algebras-folds`, fold congruence.
The observation states no crossing or runtime claim. -/
theorem reorder_eq (order beside : List Key) (neighbours : Key → List Key) :
    reorder order beside neighbours = order.mergeSort fun a b =>
      barycentreLE (barycentre order beside neighbours a) (barycentre order beside neighbours b) := by
  unfold reorder
  rw [List.map_mergeSort (s := fun a b =>
    barycentreLE (barycentre order beside neighbours a) (barycentre order beside neighbours b))
    (fun a ha b hb => by
      obtain ⟨ka, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨kb, _, rfl⟩ := List.mem_map.mp hb
      rfl)]
  simp only [List.map_map, Function.comp_def, List.map_id']

end Tools.View.Graph
