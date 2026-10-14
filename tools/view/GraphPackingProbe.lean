import Tools.View.GraphPacking
import ProofGraph.AxiomAudit

/-!
Finite independent rectangle controls and consumed scaling measurements.
Pairwise checks run only on small controls, never in the packing path or large measurements.
Run with `lake env lean --run tools/view/GraphPackingProbe.lean`.
-/

#axiom_audit Tools.View.GraphPacking

open Tools.View.GraphPacking Whatwg.Svg.Scene

namespace GraphPackingProbe

def require (holds : Bool) (message : String) : IO Unit :=
  unless holds do throw (IO.userError message)

def separated (gap : Nat) (a b : IBox) : Bool :=
  a.x1 + gap ≤ b.x0 || b.x1 + gap ≤ a.x0 ||
    a.y1 + gap ≤ b.y0 || b.y1 + gap ≤ a.y0

def verify (options : Options) (sizes : Array Size) : IO Packed := do
  let result := pack options sizes
  require (result.placements.size == sizes.size) "packing loses a rectangle"
  let occurrences := result.placements.toList.map (·.occurrence)
  require (occurrences.mergeSort (· ≤ ·) == List.range sizes.size)
    "occurrence identity is not retained"
  let area := sizes.foldl (fun total size ↦ total + size.width * size.height) 0
  require (result.itemArea == area) "item area disagrees with supplied sizes"
  for placement in result.placements do
    require (decide (placement.box.Inside result.canvas)) "rectangle exceeds canvas"
    let some original := sizes[placement.occurrence]?
      | throw (IO.userError "invalid original occurrence")
    require (placement.box.width == (original.width : Int) &&
      placement.box.height == (original.height : Int)) "packing changes rectangle dimensions"
    require (placement.oversize == decide (options.targetWidth < original.width))
      "oversize observation disagrees"
  return result

def small (options : Options) (sizes : Array Size) : IO Packed := do
  let result ← verify options sizes
  for (a, i) in result.placements.toList.zipIdx do
    for b in result.placements.toList.drop (i + 1) do
      require (decide (a.box.Disjoint b.box)) "small pairwise overlap"
      require (separated options.gap a.box b.box) "small gap control fails"
  for placement in result.placements do
    if placement.oversize then
      require ((result.placements.filter (·.shelf == placement.shelf)).size == 1)
        "oversize rectangle shares its shelf"
  return result

def controls : IO Unit := do
  let empty ← small ⟨100, 10⟩ #[]
  require (empty.rows == 0 && empty.canvas == IBox.ofSize 0 0 0) "empty packing adds a shelf"
  let single ← small ⟨100, 10⟩ #[⟨40, 30⟩]
  require (single.rows == 1 && single.canvas == IBox.ofSize 0 40 30)
    "single rectangle gains padding"
  let equal ← small ⟨100, 10⟩ #[⟨40, 20⟩, ⟨40, 20⟩, ⟨40, 20⟩]
  require (equal.placements.toList.map (·.occurrence) == [0, 1, 2])
    "equal heights lose stable order"
  require (equal.placements.toList.map (·.box) ==
    [IBox.ofSize 0 40 20, IBox.ofSize ⟨50, 0⟩ 40 20, IBox.ofSize ⟨0, 30⟩ 40 20])
    "known shelf positions disagree"
  let heights ← small ⟨100, 10⟩ #[⟨10, 10⟩, ⟨10, 30⟩, ⟨10, 20⟩]
  require (heights.placements.toList.map (·.occurrence) == [1, 2, 0]) "height ordering disagrees"
  let wide ← small ⟨50, 5⟩ #[⟨20, 40⟩, ⟨100, 30⟩, ⟨15, 20⟩, ⟨0, 20⟩, ⟨12, 10⟩]
  require (wide.rows == 3 && wide.canvas == IBox.ofSize 0 100 100 && wide.oversizeCount == 1)
    "oversize shelf policy disagrees"
  let _ ← small ⟨0, 0⟩ #[⟨0, 0⟩, ⟨0, 10⟩, ⟨20, 0⟩, ⟨0, 0⟩]
  let _ ← small ⟨0, 4⟩ #[⟨0, 0⟩, ⟨0, 10⟩, ⟨20, 0⟩, ⟨0, 0⟩]
  let _ ← small ⟨10, 0⟩ #[⟨10, 10⟩, ⟨10, 10⟩, ⟨10, 10⟩]
  let huge ← small ⟨100, 10⟩ #[⟨100000000000000000000, 5⟩, ⟨4, 3⟩]
  require (huge.canvas.width == 100000000000000000000) "natural width truncates to a machine word"
  IO.println "finite-controls,9,pass"

def sizes (count seed : Nat) : Array Size :=
  Array.ofFn (fun (i : Fin count) ↦
    { width := 40 + (i.val * 37 + seed) % 120,
      height := 24 + (i.val * 53 + seed) % 96 })

def digest (result : Packed) : UInt64 :=
  result.placements.foldl (fun value p ↦ value * 31 + hash (p.occurrence, p.box, p.shelf))
    (hash (result.canvas, result.rows, result.itemArea, result.oversizeCount))

/-- The timed input varies inside the call.
Closure construction therefore cannot precompute the packing result. -/
@[noinline] def measured (count seed : Nat) : UInt64 :=
  digest (pack ⟨1200 + seed % 7, 12⟩ (sizes count seed))

def benchmark (count repetitions : Nat) : IO Unit := do
  let sample ← verify ⟨1200, 12⟩ (sizes count 0)
  let start ← IO.monoNanosNow
  let mut checksum : UInt64 := 0
  for i in List.range repetitions do
    checksum := checksum + measured count i
  let elapsed := (← IO.monoNanosNow) - start
  IO.println (s!"{count},{repetitions},{elapsed},{sample.rows},{sample.canvas.width}," ++
    s!"{sample.canvas.height},{sample.itemArea},{sample.oversizeCount},{checksum}")

end GraphPackingProbe

def main (args : List String) : IO Unit := do
  GraphPackingProbe.controls
  if args.headD "" == "controls" then return
  IO.println ("count,repetitions,elapsed_ns,example_rows,width,height," ++
    "item_area,oversize_count,checksum")
  for (count, repetitions) in [(100, 100), (1000, 20), (10000, 4)] do
    GraphPackingProbe.benchmark count repetitions
