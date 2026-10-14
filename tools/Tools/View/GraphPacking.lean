import Whatwg.Svg.Scene.Extent

/-!
Stable shelf packing of independently rendered rectangles.
The caller supplies nonnegative envelope sizes and retains its graph data outside this module.
Oversized rectangles occupy their own shelf and widen the actual canvas.
The construction proves containment and separation, without an optimality claim.
Placement: `docs/research/2026-10-13-graph-packing-plan.md`.
-/

namespace Tools.View.GraphPacking
open Whatwg.Svg.Scene

/-- The size of one independent rendered envelope, in the caller's whole units. -/
structure Size where
  width : Nat
  height : Nat
deriving DecidableEq, Repr

/-- The shelf width target and the gap between rectangles and shelves. -/
structure Options where
  targetWidth : Nat
  gap : Nat := 0
deriving DecidableEq, Repr

/-- One original array occurrence, placed on a shelf with its own identity. -/
structure Placement where
  occurrence : Nat
  box : IBox
  shelf : Nat
  oversize : Bool
deriving DecidableEq, Repr

/-- The packed rectangles in placement order, their actual canvas and measured aggregates. -/
structure Packed where
  placements : Array Placement
  canvas : IBox
  rows : Nat
  itemArea : Nat
  oversizeCount : Nat
deriving DecidableEq, Repr

private abbrev Entry := Nat × Size

private structure State where
  placed : List Placement := []
  nextX : Nat := 0
  y : Nat := 0
  rowHeight : Nat := 0
  width : Nat := 0
  rowOpen : Bool := false
  rowBlocked : Bool := false
  rows : Nat := 0
  itemArea : Nat := 0
  oversizeCount : Nat := 0

private def push (options : Options) (state : State) (entry : Entry) (newShelf : Bool) : State :=
  let x := if newShelf then 0 else state.nextX
  let y := if newShelf then state.y + state.rowHeight + options.gap else state.y
  let height := if newShelf then entry.2.height else max state.rowHeight entry.2.height
  let rows := if state.rowOpen then (if newShelf then state.rows + 1 else state.rows) else 1
  let oversize := decide (options.targetWidth < entry.2.width)
  let placement : Placement :=
    { occurrence := entry.1, box := IBox.ofSize ⟨x, y⟩ entry.2.width entry.2.height,
      shelf := rows - 1, oversize }
  { placed := placement :: state.placed, nextX := x + entry.2.width + options.gap,
    y, rowHeight := height, width := max state.width (x + entry.2.width), rowOpen := true,
    rowBlocked := oversize, rows, itemArea := state.itemArea + entry.2.width * entry.2.height,
    oversizeCount := state.oversizeCount + (if oversize then 1 else 0) }

private def step (options : Options) (state : State) (entry : Entry) : State :=
  push options state entry (state.rowOpen &&
    (state.rowBlocked || decide (options.targetWidth < state.nextX + entry.2.width)))

private def ordered (sizes : Array Size) : List Entry :=
  (sizes.toList.zipIdx.map (fun (size, occurrence) ↦ (occurrence, size))).mergeSort
    (fun a b ↦ b.2.height ≤ a.2.height)

private def packingState (options : Options) (sizes : Array Size) : State :=
  (ordered sizes).foldl (step options) {}

/-- Sort heights stably, then pack through one shelf frontier without pairwise runtime checks. -/
def pack (options : Options) (sizes : Array Size) : Packed :=
  let state := packingState options sizes
  { placements := state.placed.reverse.toArray,
    canvas := IBox.ofSize 0 state.width (state.y + state.rowHeight), rows := state.rows,
    itemArea := state.itemArea, oversizeCount := state.oversizeCount }

/-! The erased shelf-frontier invariant serves both packing laws. -/

private def Frontier (options : Options) (state : State) (p : Placement) : Prop :=
  0 ≤ p.box.x0 ∧ 0 ≤ p.box.y0 ∧ p.box.x1 ≤ state.width ∧
    (p.box.y1 + options.gap ≤ state.y ∨
      (p.box.y0 = state.y ∧ p.box.x1 + options.gap ≤ state.nextX ∧
        p.box.y1 ≤ state.y + state.rowHeight))

private def Valid (options : Options) (state : State) : Prop :=
  (∀ p ∈ state.placed, Frontier options state p) ∧
    state.placed.Pairwise (fun a b ↦ a.box.Disjoint b.box)

/-- Empty packing has no rectangle before its frontier. A helper of both packing laws. -/
private theorem valid_empty (options : Options) : Valid options {} := by
  refine ⟨?_, List.Pairwise.nil⟩
  intro p hp
  exact False.elim (List.not_mem_nil hp)

/-- One placement retains the shelf frontier and separation.
This helper serves `pack_inside` and `pack_disjoint` under row 334 (3), concept 7 and R14. -/
private theorem push_valid (options : Options) (state : State) (entry : Entry) (newShelf : Bool)
    (hv : Valid options state) : Valid options (push options state entry newShelf) := by
  obtain ⟨frontier, clear⟩ := hv
  cases newShelf with
  | false =>
    constructor
    · intro p hp
      simp only [push, Bool.false_eq_true, if_false, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only [Frontier, push, Bool.false_eq_true, if_false, IBox.ofSize]
        refine ⟨?_, ?_, ?_, Or.inr ⟨True.intro, ?_, ?_⟩⟩ <;> omega
      · obtain ⟨hx, hy, hw, hf⟩ := frontier p hp
        simp only [Frontier, push, Bool.false_eq_true, if_false]
        refine ⟨hx, hy, ?_, ?_⟩
        · omega
        · rcases hf with old | ⟨hy, right, bottom⟩
          · exact Or.inl old
          · exact Or.inr ⟨hy, by omega, by omega⟩
    · simp only [push, Bool.false_eq_true, if_false, List.pairwise_cons]
      refine ⟨?_, clear⟩
      intro p hp
      obtain ⟨_, _, _, hf⟩ := frontier p hp
      simp only [IBox.Disjoint, IBox.ofSize]
      rcases hf with old | ⟨_, right, _⟩
      · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact Or.inr (Or.inl (by omega))
  | true =>
    constructor
    · intro p hp
      simp only [push, if_true, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only [Frontier, push, if_true, IBox.ofSize]
        refine ⟨?_, ?_, ?_, Or.inr ⟨True.intro, ?_, ?_⟩⟩ <;> omega
      · obtain ⟨hx, hy, hw, hf⟩ := frontier p hp
        simp only [Frontier, push, if_true]
        refine ⟨hx, hy, ?_, Or.inl ?_⟩
        · omega
        · rcases hf with old | ⟨_, _, bottom⟩ <;> omega
    · simp only [push, if_true, List.pairwise_cons]
      refine ⟨?_, clear⟩
      intro p hp
      obtain ⟨_, _, _, hf⟩ := frontier p hp
      simp only [IBox.Disjoint, IBox.ofSize]
      apply Or.inr
      apply Or.inr
      apply Or.inr
      rcases hf with old | ⟨_, _, bottom⟩ <;> omega

/-- A fold of placement steps retains the frontier. A helper of both packing laws. -/
private theorem fold_valid (options : Options) :
    ∀ (entries : List Entry) (state : State), Valid options state →
      Valid options (entries.foldl (step options) state)
  | [], _, hv => hv
  | entry :: entries, state, hv =>
    fold_valid options entries (step options state entry) (push_valid options state entry _ hv)

/-- Every returned rectangle lies inside the actual canvas.
Oversized and empty rectangles retain this observation.
The compound graph gallery consumes this tool law under row 334 (3), concept 7 and R14. -/
theorem pack_inside (options : Options) (sizes : Array Size) :
    ∀ p ∈ (pack options sizes).placements.toList, p.box.Inside (pack options sizes).canvas := by
  have valid : Valid options (packingState options sizes) :=
    fold_valid options (ordered sizes) {} (valid_empty options)
  intro p hp
  simp only [pack, List.toList_toArray, List.mem_reverse] at hp
  obtain ⟨hx, hy, hw, hf⟩ := valid.1 p hp
  simp only [pack, IBox.Inside, IBox.ofSize, IVec.zero_x, IVec.zero_y, Int.zero_add]
  refine ⟨hx, hw, hy, ?_⟩
  rcases hf with old | ⟨_, _, bottom⟩
  · omega
  · exact bottom

/-- Returned rectangles are pairwise disjoint; a zero gap permits touching sides.
The compound graph gallery consumes this tool law under row 334 (3), concept 7 and R14.
This observation claims no optimal area or relation between connected nodes. -/
theorem pack_disjoint (options : Options) (sizes : Array Size) :
    (pack options sizes).placements.toList.Pairwise (fun a b ↦ a.box.Disjoint b.box) := by
  have valid : Valid options (packingState options sizes) :=
    fold_valid options (ordered sizes) {} (valid_empty options)
  simp only [pack, List.toList_toArray]
  exact List.pairwise_reverse.mpr (valid.2.imp fun h ↦ h.symm)

/-- Placement retains every occurrence through the single pass. Helper of `pack_occurrences`. -/
private theorem fold_occurrences (options : Options) :
    ∀ (entries : List Entry) (state : State),
      (entries.foldl (step options) state).placed.map Placement.occurrence =
        (entries.map Prod.fst).reverse ++ state.placed.map Placement.occurrence
  | [], _ => rfl
  | entry :: entries, state => by
    rw [List.foldl_cons, fold_occurrences options entries]
    simp only [step, push, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]

/-- Every original array occurrence appears exactly once, even when sizes repeat.
The gallery's component lookup consumes this tool law under row 334 (3), concept 7 and R14. -/
theorem pack_occurrences (options : Options) (sizes : Array Size) :
    ((pack options sizes).placements.toList.map Placement.occurrence).Perm
      (List.range sizes.size) := by
  simp only [pack, List.toList_toArray, List.map_reverse, packingState, fold_occurrences,
    List.map_nil, List.append_nil, List.reverse_reverse]
  have permutation := (List.mergeSort_perm
    (sizes.toList.zipIdx.map (fun (size, occurrence) ↦ (occurrence, size)))
    (fun a b ↦ b.2.height ≤ a.2.height)).map Prod.fst
  simp only [List.map_map, Function.comp_def, List.zipIdx_map_snd, Array.length_toList,
    ← List.range_eq_range'] at permutation
  exact permutation

end Tools.View.GraphPacking
