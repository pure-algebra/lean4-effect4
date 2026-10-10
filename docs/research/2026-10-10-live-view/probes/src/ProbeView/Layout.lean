import Tools.View.Flow
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The flow's placement in linear time, equal to the tree's

`Flow.preparePlacement`, `Flow.placeWith` and `Flow.layout` (`tools/Tools/View/Flow.lean`) scan
lists in four places, so a flow of `n` items and `e` edges costs `O(n · e)`:

- `kahn` filters the whole edge list at each item it takes, and counts in-degrees by filtering;
- `orders` checks `Nodup` pairwise and finds each edge's ends by scanning the order;
- `heightAt` reads a height by a linear search of the assignments, at every edge and every item;
- `hAt` and `layout`'s `at_` index a `List` by position.

This module replaces each with a table and keeps every answer: the same order (the queue, and
each taken item's ready targets in the order `kahn` takes them, the fuel bound included), the
same check, the same assignments in the same newest-first list, and the same places. It is
checked equal to the tree's on every frame of the probe's builds (`checks/LayoutCheck.lean`).
-/

open Tools.View Tools.View.Flow

namespace Tools.View.FastLayout

/-- **Kahn's order, by in-degree counts**: `Flow.kahn`'s queue and fuel, with each item's
out-edges and the in-degrees in tables. The queue is a front list and a reversed back list. An
item taken spends all its out-edges; then its targets that no edge reaches any more join the
queue, in the order of their first edge from it. -/
def kahn (n : Nat) (es : List Edge) : List Nat :=
  let outs : Std.HashMap Nat (Array Nat) := es.foldl (fun m e => m.insert e.fr ((m.getD e.fr #[]).push e.to)) {}
  let indeg0 : Std.HashMap Nat Nat := es.foldl (fun m e => m.insert e.to (m.getD e.to 0 + 1)) {}
  -- take `k`: spend its out-edges; answer its ready targets, last first, and the counts
  let take (k : Nat) (indeg : Std.HashMap Nat Nat) : List Nat × Std.HashMap Nat Nat :=
    let targets := outs.getD k #[]
    let indeg := targets.foldl (fun m v => m.insert v (m.getD v 0 - 1)) indeg
    let ready := (targets.foldl (fun (acc : List Nat × Std.HashSet Nat) v =>
      if acc.2.contains v then acc
      else (if indeg.getD v 0 == 0 then v :: acc.1 else acc.1, acc.2.insert v)) ([], {})).1
    (ready, indeg)
  let rec go : Nat → List Nat → List Nat → Std.HashMap Nat Nat → Array Nat → Array Nat
    | 0, _, _, _, out => out
    | fuel + 1, front, back, indeg, out =>
      let next : Option (Nat × List Nat × List Nat) := match front with
        | k :: f => some (k, f, back)
        | [] => match back.reverse with
          | k :: f => some (k, f, [])
          | [] => none
      match next with
      | none => out
      | some (k, front, back) =>
        let (readyRev, indeg) := take k indeg
        go fuel front (readyRev ++ back) indeg (out.push k)
  (go (n + 1) ((List.range n).filter fun k => indeg0.getD k 0 == 0) [] indeg0 #[]).toList

/-- **`Flow.orders` by positions**: no position twice, and each edge's source before its target. -/
def orders (ord : List Nat) (es : List Edge) : Bool :=
  let (pos, dup, _) := ord.foldl (fun (acc : Std.HashMap Nat Nat × Bool × Nat) v =>
    let (m, d, i) := acc
    if m.contains v then (m, true, i + 1) else (m.insert v i, d, i + 1)) ({}, false, 0)
  !dup && es.all fun e => match pos[e.fr]?, pos[e.to]? with
    | some a, some b => a < b
    | _, _ => false

/-- `Flow.orderFor` on the fast order and check. -/
def orderFor (n : Nat) (own dag : List Edge) : List Edge × List Nat :=
  let ord := kahn n dag
  if orders ord dag then (dag, ord) else (own, List.range n)

/-- **`Flow.assignHeightsIndexed` with the heights in a table**: the same newest-first list. A
position the order names twice reads its newest height, as `heightAt` does. -/
def assignHeights (h : Nat → Int) (incoming : Tools.Graph.Index Edge) (start : Int) (ord : List Nat) :
    List (Nat × Int) :=
  (ord.foldl (fun (acc : List (Nat × Int) × Std.HashMap Nat Int) v =>
    let (out, m) := acc
    let r := relaxIndexed h incoming (fun i => m.getD i start) start v
    ((v, r) :: out, m.insert v r)) ([], {})).1

/-- `Flow.preparePlacement` on the fast order and heights. -/
def preparePlacement (b : Box) : PreparedPlacement :=
  let items := b.items.toArray
  let h (i : Nat) : Int := ((items[i]?).map itemH).getD 0
  let waits := acceptWaits b.items.length b.edges b.waitEdges
  let order := orderFor b.items.length b.edges waits.1
  { fallback := b.topPad,
    heights := assignHeights h (Tools.Graph.Index.ofList (·.to) order.1) b.topPad order.2,
    lanes := b.backs ++ waits.2 }

/-- A prepared placement's heights as a table: the newest height of each position. -/
def heightTable (pp : PreparedPlacement) : Std.HashMap Nat Int :=
  pp.heights.foldr (fun (i, y) m => m.insert i y) {}

/-- `Flow.placeWith` on the fast preparation and the height table. -/
def placeWith (width : GNode → Int) (f : Flow) : Placement :=
  let b := layWith width f
  let prepared := preparePlacement b
  let table := heightTable prepared
  { box := b, placed := atHeights (fun i => table.getD i prepared.fallback) 0 b.items,
    lanes := prepared.lanes }

/-- **`Flow.layout` in linear time**: the fast placement, and the places by position in an array. -/
def layout (f : Flow) : Laid :=
  let pl := placeWith nodeWidth f
  let b := pl.box
  let placed := pl.placed
  let arr := placed.toArray
  let at_ (i : Nat) : Option Placed := arr[i]?
  let keyAt (i : Nat) : Key := ((at_ i).map (·.key)).getD ""
  let bottomOf (p : Placed) : Int := p.y + itemH p
  let rects := b.frames.reverse.foldl (fun (rs : List (Key × Region)) fr =>
    let mine := fr.items.filterMap at_
    let inner : List Region := fr.inner.filterMap fun k => rs.lookup k
    let tops := mine.map (·.y) ++ inner.map (·.y)
    let top := tops.foldl min (tops.headD 0)
    let bot := (mine.map bottomOf ++ inner.map fun (r : Region) => r.y + r.h).foldl max 0
    let y := top - MARGIN - LABEL
    (fr.key, { key := fr.key, name := fr.name, x := fr.x, y, w := fr.w, h := bot + MARGIN - y }) :: rs) []
  let marks : List FlowMark := b.marks.filterMap fun (k, bar, is) =>
    let ps := is.filterMap at_
    match ps.head? with
    | none => none
    | some p =>
      if bar then
        let xs := ps.map Laid.middle
        some (.bar k (xs.foldl min (Laid.middle p) - CELL) (xs.foldl max (Laid.middle p) + CELL) p.y)
      else some (.diamond k (Laid.middle p) p.y)
  let routes := (b.edges.filter (·.drawn)).map (fun e =>
      let u := keyAt e.fr
      let v := keyAt e.to
      Route.down (u ++ "→" ++ v) [u, v] 1000 e.share) ++
    pl.lanes.zipIdx.map fun ((i, j), lane) =>
      let u := keyAt i
      let v := keyAt j
      if i == j then Route.loop (u ++ "↺") u else Route.back (u ++ "↺" ++ v) u v lane
  let height := (placed.map bottomOf ++ rects.map fun (p : Key × Region) => p.2.y + p.2.h).foldl max 0
  { placed := arr, routes := routes.toArray, regions := (rects.map (·.2)).reverse.toArray,
    marks := marks.toArray,
    width := b.w + (if pl.lanes.isEmpty then 0 else CELL * (GAP + 2 * pl.lanes.length)), height }

end Tools.View.FastLayout
