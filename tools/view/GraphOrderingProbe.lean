import Tools.View.Graph

/-!
Finite controls and paired measurements for the graph ordering tool.
The baseline uses the original key comparator; the candidate stores each score before sorting.
The full layout baseline changes only its rank ordering implementation.
Run with `lake env lean --run tools/view/GraphOrderingProbe.lean`.
The timings measure this Lean driver, not a renderer or scheduler.
-/

open Tools.View

namespace GraphOrderingProbe

def baselineReorder (order beside : List Key) (neighbours : Key → List Key) : List Key :=
  order.mergeSort fun a b => Graph.barycentreLE
    (Graph.barycentre order beside neighbours a) (Graph.barycentre order beside neighbours b)

def baselineOrders (g : Graph) (rk : List Nat) : List (List Key) :=
  let its := Graph.items g rk
  let top := its.foldl (fun m i => max m i.rank) 0
  let start := (List.range (top + 1)).map fun r => (its.filter (·.rank == r)).map (·.key)
  let ls := Graph.links g rk
  let ups (k : Key) := ls.filterMap fun (a, b) => if b == k then some a else none
  let downs (k : Key) := ls.filterMap fun (a, b) => if a == k then some b else none
  let down (os : List (List Key)) : List (List Key) :=
    os.zipIdx.foldl (fun (acc : List (List Key)) (o, r) =>
      acc ++ [if r == 0 then o else baselineReorder o (acc.getD (r - 1) []) ups]) []
  let up (os : List (List Key)) : List (List Key) :=
    (os.reverse.zipIdx.foldl (fun (acc : List (List Key)) (o, i) =>
      acc ++ [if i == 0 then o else baselineReorder o (acc.getD (i - 1) []) downs]) []).reverse
  up (down (up (down start)))

def baselineLayout (g : Graph) : Laid :=
  let rk := Graph.ranks g
  let its := Graph.items g rk
  let width (k : Key) : Nat := ((its.find? (·.key == k)).map (·.width)).getD GAP
  let os := baselineOrders g rk
  let ls := Graph.links g rk
  let ups (k : Key) := ls.filterMap fun (a, b) => if b == k then some a else none
  let downs (k : Key) := ls.filterMap fun (a, b) => if a == k then some b else none
  let isPoint (k : Key) : Bool := ((its.find? (·.key == k)).map (·.node.isNone)).getD false
  let centre := Tools.View.Place.centres os width ups downs ls isPoint
  let left (k : Key) : Int := (CELL / 2) * (centre.getD k 0 - width k)
  let widest : Int := (os.flatten.foldl (fun m k => max m (centre.getD k 0 + width k)) 0 + 1) / 2
  let placed : List Placed := os.zipIdx.flatMap fun (o, r) => o.map fun k =>
    { key := k, x := left k, y := ROWH * LEVEL * r, w := CELL * width k,
      node := (its.find? (·.key == k)).bind (·.node) }
  let backs := g.edges.toList.filter fun e => e.dst < e.src
  let key (i : Nat) : Key := ((g.nodes[i]?).map (·.key)).getD ""
  let routes : List Route :=
    ((g.edges.toList.filter fun e => e.src < e.dst).map fun e => Route.down e.key (Graph.chain g rk e)) ++
    (backs.zipIdx.map fun (e, lane) => Route.back e.key (key e.src) (key e.dst) lane) ++
    ((g.edges.toList.filter fun e => e.src = e.dst).map fun e => Route.loop e.key (key e.src))
  let ranksN : Int := os.length
  { placed := placed.toArray, routes := routes.toArray,
    width := CELL * (widest + (if backs.isEmpty then 0 else GAP + 2 * backs.length)),
    height := if ranksN == 0 then 0 else ROWH * LEVEL * (ranksN - 1) + ROWH * BOXROWS }

def nodeKey (i : Nat) : Key := s!"node-{i}"

def layered (width : Nat) : Graph :=
  { nodes := ((List.range (2 * width)).map fun i => { key := nodeKey i, line1 := "node" }).toArray,
    edges := ((List.range width).flatMap fun i => (List.range 3).map fun j =>
      { key := s!"edge-{i}-{j}", src := i, dst := width + (width - 1 - i + j) % width }).toArray }

def incoming (links : List (Key × Key)) (k : Key) : List Key :=
  links.filterMap fun (a, b) => if b == k then some a else none

def orderDigest (order : List Key) : UInt64 := order.foldl (fun h k => h * 31 + hash k) 0

def layoutDigest (laid : Laid) : UInt64 :=
  laid.placed.foldl (fun h p => h * 31 + hash (p.key, p.x, p.y, p.w))
    (hash (laid.width, laid.height, laid.routes.size))

/-- Vary the argument inside the timed call, so closure creation cannot precompute its result. -/
@[noinline] def orderingDigest (candidate : Bool) (order beside : List Key)
    (links : List (Key × Key)) (nonce : Nat) : UInt64 :=
  let order := order.rotateLeft nonce
  orderDigest (if candidate then Graph.reorder order beside (incoming links)
    else baselineReorder order beside (incoming links))

/-- Rotate edge order inside the timed call without changing the layered graph's incidence. -/
@[noinline] def layeredDigest (candidate : Bool) (g : Graph) (nonce : Nat) : UInt64 :=
  let g := { g with edges := (g.edges.toList.rotateLeft nonce).toArray }
  layoutDigest (if candidate then Graph.layout g else baselineLayout g)

def elapsed (repetitions : Nat) (action : Nat → UInt64) : IO (Nat × UInt64) := do
  let start ← IO.monoNanosNow
  let mut digest : UInt64 := 0
  for i in List.range repetitions do
    digest := digest + action i
  let stop ← IO.monoNanosNow
  return (stop - start, digest)

def controls : IO Unit := do
  let cases : List (List Key × List Key × List (Key × List Key)) :=
    [([], [], []), (["a"], [], []),
     (["a", "b", "a", "c"], ["x", "x", "y"],
       [("a", ["missing", "x"]), ("b", ["y", "x"]), ("c", [])]),
     (["a", "b", "c"], ["x", "y"], [("a", ["x", "y"]), ("b", ["y", "x"]), ("c", ["missing"])]),
     (["a", "a", "b"], [], [("a", ["missing"]), ("b", ["missing"])])]
  for (order, beside, table) in cases do
    let neighbours (k : Key) := (table.lookup k).getD []
    unless Graph.reorder order beside neighbours == baselineReorder order beside neighbours do
      throw (IO.userError "ordering control disagrees")
  IO.println s!"controls,{cases.length},pass"

def ordering (width repetitions : Nat) : IO Unit := do
  let g := layered width
  let rk := Graph.ranks g
  let links := Graph.links g rk
  let beside := (List.range width).map nodeKey
  let order := (List.range width).map fun i => nodeKey (width + i)
  let baseline := baselineReorder order beside (incoming links)
  let candidate := Graph.reorder order beside (incoming links)
  unless baseline == candidate do throw (IO.userError "layered ordering disagrees")
  let (before, oldDigest) ← elapsed repetitions (orderingDigest false order beside links)
  let (after, newDigest) ← elapsed repetitions (orderingDigest true order beside links)
  unless oldDigest == newDigest do throw (IO.userError "ordering checksum disagrees")
  IO.println s!"ordering,{width},{g.nodes.size},{g.edges.size},{repetitions},{before},{after},{oldDigest}"

def layout (width repetitions : Nat) : IO Unit := do
  let g := layered width
  let baseline := baselineLayout g
  let candidate := Graph.layout g
  unless baseline == candidate do throw (IO.userError "layered layout disagrees")
  let (before, oldDigest) ← elapsed repetitions (layeredDigest false g)
  let (after, newDigest) ← elapsed repetitions (layeredDigest true g)
  unless oldDigest == newDigest do throw (IO.userError "layout checksum disagrees")
  IO.println s!"layout,{width},{g.nodes.size},{g.edges.size},{repetitions},{before},{after},{oldDigest}"

end GraphOrderingProbe

def main (args : List String) : IO Unit := do
  GraphOrderingProbe.controls
  IO.println "case,width,nodes,edges,repetitions,baseline_ns,candidate_ns,checksum"
  if args.headD "" == "controls" then return
  let orderCases := if args.headD "" == "quick" then [(32, 8), (128, 3), (512, 1)]
    else [(32, 8), (128, 3), (512, 1), (2048, 1)]
  for (width, repetitions) in orderCases do
    GraphOrderingProbe.ordering width repetitions
  for (width, repetitions) in [(16, 2), (32, 2), (64, 1), (128, 1)] do
    GraphOrderingProbe.layout width repetitions
