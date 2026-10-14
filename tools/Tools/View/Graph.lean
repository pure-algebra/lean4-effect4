import Tools.View.Place
import Tools.View.GraphOrdering
import Tools.View.Organic
import Tools.View.ConnectorMemo
import Tools.View.PaintBounds

/-!
# A graph: ranks, order, places, routes

The graph view's building blocks (decisions row 336; `docs/research/2026-10-09-visual-pipeline.md`).
A graph is nodes in an order, and edges between them. It need not be a tree, and it may have
cycles. The drawing is a layered one in four steps, each a function of the graph and the step
before, with no engine:

1. **Back edges by the order.** An edge from an earlier node to a later one is forward. Every
   other edge is a back edge: a loop's return, or a cycle of waits. So the forward edges form a
   graph with no cycle, and its order is the nodes' own.
2. **Ranks.** A node's rank is the length of the longest forward path into it, computed in the
   nodes' order (`ranks`). Every forward edge descends at least one rank (`ranks_forward`).
3. **Order and places.** A forward edge that spans several ranks passes through one point in each
   rank between. Each rank is ordered by the barycentre of its neighbours in the rank above, then
   below. Each item then stands across by Brandes and Köpf (`Tools.View.Place`): aligned with
   its neighbours' medians, so most edges run straight and a long edge's run stays straight.
4. **Routes.** Each edge is its own path of cubic segments. A forward edge leaves the middle of
   its source's bottom and steps down to the middle of its target's top, passing straight through
   each rank between. A step is vertical at both ends, so it bends only where the edge moves
   across: the edge aligned with its box runs straight, and the others branch from it. A back edge is one arc out of its
   source's right side, through a lane of its own at the right, into its target's right side. An
   edge from a node to itself is a small drop off its right side.

Every node, point and edge keeps its key, and a box's growth and an edge's reveal are fields of
the layout: a still layout has both at rest. So a transition is a sampled layout
(`Tools.View.Motion`), and one drawing serves both.

The order of the nodes is the caller's: a run's fibers by their identities, a program's nodes by
their addresses. A different order gives other back edges, and the same forward law.
-/

namespace Tools.View

/-- A node: its key, two short lines of text, and whether it is lit. -/
structure GNode where
  key : Key
  line1 : String
  line2 : String := ""
  lit : Bool := false
deriving DecidableEq, Repr

/-- An edge between two nodes, by their positions in the graph's order. -/
structure GEdge where
  key : Key
  src : Nat
  dst : Nat
deriving Repr

/-- A graph: its nodes in their order, and its edges. -/
structure Graph where
  nodes : Array GNode := #[]
  edges : Array GEdge := #[]
deriving Repr

namespace Graph

/-! ## Ranks, and the forward law -/

/-- The sources of the forward edges into `v`. -/
def preds (g : Graph) (v : Nat) : List Nat :=
  g.edges.toList.filterMap fun e => if e.dst = v ∧ e.src < v then some e.src else none

/-- The rank of `v`, from the ranks of the nodes before it: one more than the largest rank of a
forward source, or 0. -/
def rankOf (g : Graph) (acc : List Nat) (v : Nat) : Nat :=
  (preds g v).foldl (fun m u => max m (acc.getD u 0 + 1)) 0

/-- One step of the ranking: the next node's rank, after the ranks before it. -/
def rankStep (g : Graph) (acc : List Nat) (v : Nat) : List Nat := acc ++ [rankOf g acc v]

/-- The ranks of the first `k` nodes. -/
def ranksUpTo (g : Graph) (k : Nat) : List Nat := (List.range k).foldl (rankStep g) []

/-- **The ranks** of a graph's nodes, in their order. -/
def ranks (g : Graph) : List Nat := ranksUpTo g g.nodes.size

theorem ranksUpTo_succ (g : Graph) (k : Nat) :
    ranksUpTo g (k + 1) = ranksUpTo g k ++ [rankOf g (ranksUpTo g k) k] := by
  simp only [ranksUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    rankStep]

theorem length_ranksUpTo (g : Graph) (k : Nat) : (ranksUpTo g k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ranksUpTo_succ, List.length_append, ih, List.length_singleton]

/-- A rank, once computed, stays: the ranks of more nodes extend those of fewer. -/
theorem ranksUpTo_getD_stable (g : Graph) {j k : Nat} (hj : j < k) :
    ∀ m, k ≤ m → (ranksUpTo g m).getD j 0 = (ranksUpTo g k).getD j 0 := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, ranksUpTo_succ, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [length_ranksUpTo]; omega), ← List.getD_eq_getElem?_getD]
    exact ih

/-- The rank of `v` is its own step's. -/
theorem ranksUpTo_getD_self (g : Graph) (v : Nat) :
    (ranksUpTo g (v + 1)).getD v 0 = rankOf g (ranksUpTo g v) v := by
  rw [ranksUpTo_succ, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_ranksUpTo]; exact Nat.le_refl v),
    length_ranksUpTo, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

/-- A fold of `max` is at least each of its terms. -/
theorem le_foldl_max (f : Nat → Nat) :
    ∀ (l : List Nat) (init u : Nat), u ∈ l → f u ≤ l.foldl (fun m x => max m (f x)) init
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, init, u, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right init (f u)) (init_le_foldl_max f xs _)
    · exact le_foldl_max f xs _ u h
where
  /-- A fold of `max` is at least its start. -/
  init_le_foldl_max (f : Nat → Nat) : ∀ (l : List Nat) (init : Nat),
      init ≤ l.foldl (fun m x => max m (f x)) init
    | [], _ => Nat.le_refl _
    | x :: xs, init => by
      rw [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left init (f x)) (init_le_foldl_max f xs _)

/-- **The forward law.** Every forward edge descends at least one rank. -/
theorem ranks_forward (g : Graph) (e : GEdge) (he : e ∈ g.edges.toList) (hf : e.src < e.dst)
    (hd : e.dst < g.nodes.size) :
    (ranks g).getD e.src 0 < (ranks g).getD e.dst 0 := by
  have hu : e.src ∈ preds g e.dst :=
    List.mem_filterMap.mpr ⟨e, he, by simp only [true_and, hf, if_true]⟩
  have step := le_foldl_max (fun u => (ranksUpTo g e.dst).getD u 0 + 1) _ 0 _ hu
  have hv : (ranks g).getD e.dst 0 = rankOf g (ranksUpTo g e.dst) e.dst := by
    rw [ranks, ranksUpTo_getD_stable g (Nat.lt_succ_self e.dst) _ hd, ranksUpTo_getD_self]
  have hsrc : (ranks g).getD e.src 0 = (ranksUpTo g e.dst).getD e.src 0 :=
    ranksUpTo_getD_stable g hf _ (Nat.le_of_lt hd)
  rw [hv, hsrc]
  exact step

end Graph

/-! ## Places -/

/-- A placed item: a node's box, or a point that a long edge passes through. Places are in
logical pixels from the graph's own top left. -/
structure Placed where
  key : Key
  x : Int
  y : Int
  w : Int
  node : Option GNode := none
  /-- how far a box has grown about its centre, per mille; 1000 at rest -/
  grow : Nat := 1000
deriving DecidableEq, Repr

/-- A route: a forward edge through its items, from its source to its target; a back edge, with
its source, its target and its lane at the right; or an edge from a node to itself. Each is drawn
from its source as far as its reveal, per mille; 1000 at rest. A forward edge carries its share of
the work, in millionths, which sets its width by da Vinci's rule (`Tools.View.Grow.split`). -/
inductive Route where
  | down (key : Key) (items : List Key) (reveal : Nat := 1000) (share : Nat := 1000000)
  | back (key : Key) (src dst : Key) (lane : Nat) (reveal : Nat := 1000)
  | loop (key : Key) (node : Key) (reveal : Nat := 1000)
deriving DecidableEq, Repr

namespace Route

/-- A route's key. -/
def key : Route → Key
  | .down k _ _ _ | .back k _ _ _ _ | .loop k _ _ => k

/-- A route's reveal. -/
def reveal : Route → Nat
  | .down _ _ r _ | .back _ _ _ _ r | .loop _ _ r => r

/-- A route with another reveal. -/
def withReveal (r : Nat) : Route → Route
  | .down k ks _ sh => .down k ks r sh
  | .back k s d lane _ => .back k s d lane r
  | .loop k n _ => .loop k n r

/-- A route keeps itself under its own reveal. -/
theorem withReveal_self (rt : Route) : rt.withReveal rt.reveal = rt := by
  cases rt <;> rfl

end Route

/-- A region of a laid-out graph: a bracket around the items of one region of the program (a
scope, a fork's fiber, an uninterruptible span, a provided layer), with its name. -/
structure Region where
  key : Key
  name : String
  x : Int
  y : Int
  w : Int
  h : Int
deriving DecidableEq, Repr

/-- A mark of a program's flow, in the notation of UML's activity diagrams: a bar where branches
that all run part or meet, from `x0` to `x1` at height `y`; a diamond where alternatives part
or meet, centred at `(x, y)`. Logical bar contacts include both endpoints. -/
inductive FlowMark where
  | bar (key : Key) (x0 x1 y : Int)
  | diamond (key : Key) (x y : Int)
deriving DecidableEq, Repr

/-- The identity of a bar or diamond. -/
def FlowMark.key : FlowMark → Key
  | .bar k .. | .diamond k .. => k

/-- A placed point attached to a named mark. Geometry and identity remain separate data. -/
structure PortAttachment where
  port : Key
  mark : Key
deriving DecidableEq, Repr

/-- A laid-out graph: its placed items, its routes, its regions and its marks, and its size in
logical pixels. -/
structure Laid where
  placed : Array Placed := #[]
  routes : Array Route := #[]
  width : Int := 0
  height : Int := 0
  regions : Array Region := #[]
  marks : Array FlowMark := #[]
  attachments : Array PortAttachment := #[]
  /-- The span used by return lanes, independent of any later canvas expansion. -/
  routingWidth : Option Int := none
deriving DecidableEq, Repr

/-- The lane span, with the original canvas-width convention for legacy layouts. -/
def Laid.routeWidth (l : Laid) : Int := l.routingWidth.getD l.width

namespace Graph

/-- An item of the order: its key, its rank, its width in cells, and its node, if it is one. -/
structure Item where
  key : Key
  rank : Nat
  width : Nat
  node : Option GNode

/-- The key of the point at rank `r` of the edge `k`. -/
def pointKey (k : Key) (r : Nat) : Key := k ++ "@" ++ toString r

/-- The width in cells of a node's box: its longer line and a cell each side; six at least. -/
def boxWidth (n : GNode) : Nat := max BOX_MIN (max n.line1.length n.line2.length + BOX_PAD)

/-- A forward edge's items, from its source to its target, through a point at each rank between. -/
def chain (g : Graph) (rk : List Nat) (e : GEdge) : List Key :=
  let rs := rk.getD e.src 0
  let rd := rk.getD e.dst 0
  let src := ((g.nodes[e.src]?).map (·.key)).getD ""
  let dst := ((g.nodes[e.dst]?).map (·.key)).getD ""
  [src] ++ ((List.range (rd - rs - 1)).map fun i => pointKey e.key (rs + 1 + i)) ++ [dst]

/-- The items of every rank: the nodes, then the points of the long forward edges. -/
def items (g : Graph) (rk : List Nat) : List Item :=
  (g.nodes.toList.zipIdx.map fun (n, i) => ⟨n.key, rk.getD i 0, boxWidth n, some n⟩) ++
    (g.edges.toList.filter (fun e => e.src < e.dst)).flatMap fun e =>
      let rs := rk.getD e.src 0
      (List.range (rk.getD e.dst 0 - rs - 1)).map fun i => ⟨pointKey e.key (rs + 1 + i), rs + 1 + i, GAP, none⟩

/-- The links between two adjacent ranks: each step of a forward edge's chain. -/
def links (g : Graph) (rk : List Nat) : List (Key × Key) :=
  (g.edges.toList.filter (fun e => e.src < e.dst)).flatMap fun e =>
    let c := chain g rk e
    c.zip c.tail

/-- **The order of each rank**: the items' own order, then two sweeps down and up by barycentres. -/
def orders (g : Graph) (rk : List Nat) : List (List Key) :=
  let its := items g rk
  let top := its.foldl (fun m i => max m i.rank) 0
  let start := (List.range (top + 1)).map fun r => (its.filter (·.rank == r)).map (·.key)
  let ls := links g rk
  let ups (k : Key) := ls.filterMap fun (a, b) => if b == k then some a else none
  let downs (k : Key) := ls.filterMap fun (a, b) => if a == k then some b else none
  let down (os : List (List Key)) : List (List Key) :=
    (os.zipIdx.foldl (fun (acc : List (List Key)) (o, r) =>
      acc ++ [if r == 0 then o else reorder o (acc.getD (r - 1) []) ups]) [])
  let up (os : List (List Key)) : List (List Key) :=
    ((os.reverse.zipIdx.foldl (fun (acc : List (List Key)) (o, i) =>
      acc ++ [if i == 0 then o else reorder o (acc.getD (i - 1) []) downs]) []).reverse)
  up (down (up (down start)))

/-- **The layout** of a graph: the ranks, the order of each rank, each item's place across by
Brandes and Köpf (`Tools.View.Place.centres`), the routes, and the lanes of the back edges. -/
def layout (g : Graph) : Laid :=
  let rk := ranks g
  let its := items g rk
  let width (k : Key) : Nat := ((its.find? (·.key == k)).map (·.width)).getD GAP
  let os := orders g rk
  let ls := links g rk
  let ups (k : Key) := ls.filterMap fun (a, b) => if b == k then some a else none
  let downs (k : Key) := ls.filterMap fun (a, b) => if a == k then some b else none
  let isPoint (k : Key) : Bool := ((its.find? (·.key == k)).map (·.node.isNone)).getD false
  let centre := Place.centres os width ups downs ls isPoint
  -- a centre in half cells, less the item's width, is its left edge in half cells: four pixels each
  let left (k : Key) : Int := (CELL / 2) * (centre.getD k 0 - width k)
  let widest : Int := (os.flatten.foldl (fun m k => max m (centre.getD k 0 + width k)) 0 + 1) / 2
  let placed : List Placed := os.zipIdx.flatMap fun (o, r) =>
    o.map fun k =>
      { key := k, x := left k, y := ROWH * LEVEL * r, w := CELL * width k,
        node := (its.find? (·.key == k)).bind (·.node) }
  let backs := g.edges.toList.filter fun e => e.dst < e.src
  let key (i : Nat) : Key := ((g.nodes[i]?).map (·.key)).getD ""
  let routes : List Route :=
    ((g.edges.toList.filter fun e => e.src < e.dst).map fun e => Route.down e.key (chain g rk e)) ++
      (backs.zipIdx.map fun (e, lane) => Route.back e.key (key e.src) (key e.dst) lane) ++
      ((g.edges.toList.filter fun e => e.src = e.dst).map fun e => Route.loop e.key (key e.src))
  let ranksN : Int := os.length
  let routingWidth := CELL * (widest + (if backs.isEmpty then 0 else GAP + 2 * backs.length))
  let allocatedHeight := if ranksN == 0 then 0 else ROWH * LEVEL * (ranksN - 1) + ROWH * BOXROWS
  let loops := routes.filterMap fun
    | .loop _ k _ => (placed.find? (·.key == k)).map fun p =>
      let centre := p.y + (if p.node.isSome then ROWH * BOXROWS / 2 else ROWH)
      PaintBounds.controlHull (PaintBounds.loopSegment (p.x + p.w) centre LOOP_HALF LOOP_REACH)
    | _ => none
  let (width, height) := PaintBounds.reserveCanvas routingWidth allocatedHeight loops
  { placed := placed.toArray, routes := routes.toArray,
    width, height, routingWidth := some routingWidth }

end Graph

/-! ## The drawing -/

namespace Laid

/-- The placed item with key `k`. -/
def find (l : Laid) (k : Key) : Option Placed := l.placed.find? (·.key == k)

/-- The painted bounds of a box at its current growth, in logical pixels. -/
def boxBounds (p : Placed) : Rect :=
  let w := p.w * p.grow / 1000
  let h := ROWH * BOXROWS * p.grow / 1000
  let x := p.x + (p.w - w) / 2
  let y := p.y + (ROWH * BOXROWS - h) / 2
  ⟨x, y, x + w, y + h⟩

/-- A box, grown about its centre as far as its `grow`: its ground, its band when lit, its frame;
its two lines and its pointer box once it has grown whole. -/
def boxCalls (L : Look) (dx dy : Int) (p : Placed) (n : GNode) : List (Keyed Call) :=
  if p.grow = 0 then [] else
  let h := ROWH * BOXROWS
  let bounds := boxBounds p
  let w' := bounds.x1 - bounds.x0
  let h' := bounds.y1 - bounds.y0
  let x := dx + bounds.x0
  let y := dy + bounds.y0
  let room : Int := p.w / CELL - 2
  let r : Int := L.strokes.radius
  let m (v : Int) : Int := 1000 * v
  let surface : List (Keyed Call) :=
    if r = 0 then
      [⟨p.key, .fill .ground 1000 x y w' h'⟩] ++
        (if n.lit then [⟨p.key, .fill .rule L.band x y w' h'⟩] else []) ++
        [⟨p.key, .frame .ink x y w' h' L.strokes.frame⟩]
    else
      [⟨p.key, .shape .ground 1000 [Grow.roundRect (m x) (m y) (m w') (m h') r]⟩] ++
        (if n.lit then [⟨p.key, .shape .rule L.band [Grow.roundRect (m x) (m y) (m w') (m h') r]⟩] else []) ++
        [⟨p.key, .shape .ink 1000 (Grow.ring (m x) (m y) (m w') (m h') r (m L.strokes.frame))⟩]
  surface ++
    (if 1000 ≤ p.grow then
      cellsAt p.key (dx + p.x + CELL) (dy + p.y + BASE) n.line1 room ++
        cellsAt p.key (dx + p.x + CELL) (dy + p.y + ROWH + BASE) n.line2 room ++
        [⟨p.key, .hit (dx + p.x) (dy + p.y) p.w h⟩]
    else [])

/-- A point of a route, in the graph's own logical pixels. -/
abbrev Pt := Int × Int

/-- The middle of an item across: a box's middle, or a point's pass. -/
def middle (p : Placed) : Int := p.x + (if p.node.isSome then p.w / 2 else CELL)

/-- Where an edge leaves an item downward: the middle of its bottom; a point has no height, so an
edge leaves it where it enters. Every edge of a box leaves
from one point and enters at one point, so the edge aligned with the box (`Tools.View.Place`)
runs straight and the others branch from it, as a tree's limbs do. -/
def exitAt (p : Placed) : Pt :=
  if p.node.isSome then
    let b := boxBounds p
    (b.x0 + (b.x1 - b.x0) / 2, b.y1)
  else (middle p, p.y)

/-- Where an edge enters an item from above: the middle of its top. -/
def entryAt (p : Placed) : Pt :=
  if p.node.isSome then
    let b := boxBounds p
    (b.x0 + (b.x1 - b.x0) / 2, b.y0)
  else (middle p, p.y)

/-- A straight segment from `a` to `b`. -/
def straight (a b : Pt) : Cubic := ⟨a, a, b, b⟩

/-- **A step down** from `a` to `b`, in the look's form (`Curve`). A `bumpY` step is one cubic
segment, vertical at both ends, each control `reach` per mille of the drop from its end: at 500,
half the drop, it is d3's vertical link and dot's spline between ranks. A `stepY` step turns at
the middle of the drop. Two ends in one column make a straight step in every form: a route bends
only where it moves across. -/
def stepDown (L : Look) (a b : Pt) : List Cubic :=
  match L.curve with
  | .bumpY =>
    let h := (b.2 - a.2) * L.reach / 1000
    [⟨a, (a.1, a.2 + h), (b.1, b.2 - h), b⟩]
  | .linear => [straight a b]
  | .stepY =>
    if a.1 = b.1 then [straight a b] else
    let m := (a.2 + b.2) / 2
    [straight a (a.1, m), straight (a.1, m) (b.1, m), straight (b.1, m) b]

/-- **A route as cubic segments**, from its source to its target. A forward route leaves the
middle of its source's bottom, steps down to each point and passes straight through the point's
rank, then steps down to the middle of its target's top. A back route is one arc: out of its source's right side, around
through its lane, into its target's right side, so a return reads as a return. A loop is a small
drop off a box's right side. `find` answers an item's place by its key, and `width` is the graph's
width, whose right side holds the lanes. -/
def segments (L : Look) (find : Key → Option Placed) (width : Int) : Route → List Cubic
  | .down _ ks _ _ =>
    let ps := ks.filterMap find
    if ps.length != ks.length then [] else
    match ps with
    | [] => []
    | a :: rest =>
      let n := rest.length
      (rest.zipIdx.foldl (fun (acc : List Cubic × Pt) (b, i) =>
        if i + 1 == n then
          let into := entryAt b
          (acc.1 ++ stepDown L acc.2 into, into)
        else
          let into : Pt := (middle b, b.y)
          let out : Pt := (middle b, b.y + ROWH * BOXROWS)
          (acc.1 ++ stepDown L acc.2 into ++ [straight into out], out)) ([], exitAt a)).1
  | .back _ s d lane _ =>
    match find s, find d with
    | some a, some b =>
      let lx := width - CELL * (2 * lane + 1)
      -- a box's side at its middle row; a point has no height, and is its own side
      let side (p : Placed) (rise : Int) : Pt :=
        if p.node.isSome then
          let b := boxBounds p
          (b.x1, b.y0 + (b.y1 - b.y0) / 2 - rise * p.grow / 1000)
        else (p.x + 2 * CELL, p.y)
      let p : Pt := side a 0
      let q : Pt := side b BACK_RISE
      -- controls a third past the lane, so the arc's widest point reaches the lane
      let cx := lx + (lx - max p.1 q.1) / 3
      [⟨p, (cx, p.2), (cx, q.2), q⟩]
    | _, _ => []
  | .loop _ k _ =>
    match find k with
    | some a =>
      let b := boxBounds a
      let x := if a.node.isSome then b.x1 else a.x + a.w
      let y := if a.node.isSome then b.y0 + (b.y1 - b.y0) / 2 else a.y + ROWH
      let half := if a.node.isSome then LOOP_HALF * a.grow / 1000 else LOOP_HALF
      [PaintBounds.loopSegment x y half LOOP_REACH]
    | none => []

/-- **The segments revealed from their start for `budget` of size**: each whole segment within the
budget, then the part of the next one that the budget reaches. -/
def revealed : List Cubic → Int → List Cubic
  | [], _ => []
  | c :: rest, budget =>
    if budget ≤ 0 then []
    else if c.size ≤ budget then c :: revealed rest (budget - c.size)
    else [c.upTo (budget * 1000 / c.size)]

/-- **Segments drawn from their start for `budget` of size**: each whole segment within the budget,
then the part of the next one that the budget reaches. -/
def drawn (key : Key) (weight : Nat) (dx dy : Int) : List Cubic → Int → List (Keyed Call)
  | [], _ => []
  | c :: rest, budget =>
    if budget ≤ 0 then []
    else if c.size ≤ budget then
      ⟨key, .curve .ink (c.move dx dy) weight⟩ :: drawn key weight dx dy rest (budget - c.size)
    else [⟨key, .curve .ink ((c.upTo (budget * 1000 / c.size)).move dx dy) weight⟩]

/-- The length of an arrowhead's two strokes, along and across, in logical pixels. -/
def HEAD_ALONG : Int := 6
def HEAD_ACROSS : Int := 4

/-- **An arrowhead** where a segment ends: two short strokes back from its end, along the segment's
last direction, its dominant axis. Drawn only where the layout does not show the direction: an
arc in a lane (decisions row 337, point 1). -/
def arrowhead (key : Key) (weight : Nat) (dx dy : Int) (c : Cubic) : List (Keyed Call) :=
  let (ex, ey) := c.p3
  let ddx := c.p3.1 - c.p2.1
  let ddy := c.p3.2 - c.p2.2
  let back : Pt × Pt :=
    if ddx.natAbs ≥ ddy.natAbs then
      let s := if ddx ≥ 0 then -HEAD_ALONG else HEAD_ALONG
      ((ex + s, ey - HEAD_ACROSS), (ex + s, ey + HEAD_ACROSS))
    else
      let s := if ddy ≥ 0 then -HEAD_ALONG else HEAD_ALONG
      ((ex - HEAD_ACROSS, ey + s), (ex + HEAD_ACROSS, ey + s))
  [⟨key, .curve .ink ((straight back.1 c.p3).move dx dy) weight⟩,
   ⟨key, .curve .ink ((straight back.2 c.p3).move dx dy) weight⟩]

/-- The half size of a diamond, and the thickness of a bar, in logical pixels. -/
def DIAMOND : Int := 5
def BAR : Int := 3

/-- Whether an item is a point on a bar of the layout: a fork's or a join's port. -/
def onBar (l : Laid) (p : Placed) : Bool :=
  p.node.isNone && l.marks.toList.any fun
    | .bar _ x0 x1 y => y == p.y && x0 ≤ middle p && middle p ≤ x1
    | _ => false

/-! ### The drawing on a key index and a stroke cache

`Laid.find` scans the placed items at every key a route names, and `Laid.onBar` scans every mark.
A drawing builds the index of its places once (`Ix`), which answers as they do (`Ix.find_of`,
`Ix.onBar_of`). A cache keeps each connector outline at the origin by all its construction inputs.
The key includes the docking offsets and radii.
A sequence of frames threads one cache, whose answers satisfy `Connector.cached_eq`.
The next frame receives a valid cache by `Connector.cached_valid`. -/

/-- **A laid graph's places by key**, built once per drawing, and the bars of its marks. -/
structure Ix where
  places : KeyMap Key Placed
  bars : List (Int × Int × Int)

/-- The index of a laid graph. Its places are put last first, so the first place of a key stands,
as `Laid.find` answers. -/
def Ix.of (l : Laid) : Ix where
  places := KeyMap.firstBy Placed.key l.placed.toList
  bars := l.marks.toList.filterMap fun
    | .bar _ x0 x1 y => some (x0, x1, y)
    | _ => none

/-- The place of a key, by the index. -/
def Ix.find (ix : Ix) (k : Key) : Option Placed := ix.places.get? k

/-- Whether an item is a point on a bar, by the index. -/
def Ix.onBar (ix : Ix) (p : Placed) : Bool :=
  p.node.isNone && ix.bars.any fun (x0, x1, y) => y == p.y && x0 ≤ middle p && middle p ≤ x1

/-- **The index answers as `Laid.find` does**, at every key. A tool law; its consumer is the
drawing on the index (`callsCached`). Placement: concept `initial-algebras-folds`, R14's live
authoring. -/
theorem Ix.find_of (l : Laid) (k : Key) : (Ix.of l).find k = l.find k := by
  simp only [Ix.of, Ix.find, Laid.find, ← Array.find?_toList]
  exact KeyMap.get?_firstBy _ _ _

/-- **The index answers as `Laid.onBar` does**, at every item. A tool law; its consumer is the
drawing on the index (`callsCached`). Placement: concept `initial-algebras-folds`, R14's live
authoring. -/
theorem Ix.onBar_of (l : Laid) (p : Placed) : (Ix.of l).onBar p = l.onBar p := by
  simp only [Ix.of, Ix.onBar, Laid.onBar]
  congr 1
  induction l.marks.toList with
  | nil => rfl
  | cons m ms ih =>
    cases m with
    | bar k x0 x1 y => simp only [List.filterMap_cons, List.any_cons, ih]
    | diamond k x y => simp only [List.filterMap_cons, List.any_cons, ih, Bool.false_or]

/-- The graph retains complete connector outlines, including their docking geometry. -/
abbrev StrokeCache := Connector.Cache

/-- The bar's top in logical pixels. Odd heights use the painter's integer origin. -/
def barTop (y : Int) : Int := y - BAR / 2

/-- The bar surface relative to its route point, in thousandths. -/
def barSurface (down : Bool) : Int := 1000 * (barTop 0 + if down then BAR else 0)

/-- A forward edge is one closed connector outline with integrated flares at its docking surfaces.
The width follows its share, bounded below by the look's finest line.
While it grows, its tip narrows. -/
def organicCalls (find : Key → Option Placed) (onBar : Placed → Bool) (L : Look) (cache : StrokeCache)
    (key : Key) (ks : List Key) (share : Nat) (cs : List Cubic) (whole : Bool) :
    List (Keyed Call) × StrokeCache :=
  let o := L.organic
  let w : Int := max (o.fine : Int) ((o.trunk : Int) * share / 1000000)
  let R : Int := (o.flare : Int) * w / max 1 (o.trunk : Int)
  -- A collar uses the painted surface and the straight room before a rounded box corner.
  let surface (down : Bool) (k : Key) : Option (Int × Int) := (find k).bind fun p =>
    if p.node.isSome then
      let bounds := boxBounds p
      let room := 1000 * (bounds.x1 - bounds.x0) / 2 - w / 2 - L.strokes.radius
      if p.grow = 0 then none else some (0, min R (max 0 room))
    else if onBar p then some (barSurface down, R) else none
  let source := (ks.head?.bind (surface true)).map fun (off, r) =>
    ({ offset := off, radius := r } : Connector.Dock)
  let target := if whole then (ks.getLast?.bind (surface false)).map fun (off, r) =>
    ({ offset := off, radius := r } : Connector.Dock) else none
  match cs with
  | [] => ([], cache)
  | c :: _ =>
    let request : Connector.Request := {
      seed := Grow.seedOf key, noise := o.noise, wave := o.wave, width := w, tip := !whole,
      segments := cs.map (Cubic.move (-c.p0.1) (-c.p0.2)), source, target }
    let (outline, cache) := Connector.cached cache request
    let body := outline.map (Cubic.move (1000 * c.p0.1) (1000 * c.p0.2))
    if body.isEmpty then ([], cache) else ([⟨key, .shape .ink 1000 [body]⟩], cache)

/-- A route's calls, on a stroke cache: its segments, drawn as far as its reveal, at the look's
weight of an edge, or, for a forward edge in a look with a trunk, as an organic stroke; an arc in a
lane, drawn whole, ends in an arrowhead. -/
def routeCalls (L : Look) (find : Key → Option Placed) (onBar : Placed → Bool) (width : Int)
    (dx dy : Int) (cache : StrokeCache) (rt : Route) : List (Keyed Call) × StrokeCache :=
  let cs := segments L find width rt
  let budget : Int := (cs.map (·.size)).foldl (· + ·) 0 * rt.reveal / 1000
  let body := drawn rt.key L.strokes.edge dx dy cs budget
  match rt, cs.getLast? with
  | .down key ks _ share, _ =>
    if L.organic.trunk = 0 then (body, cache)
    else organicCalls find onBar L cache key ks share ((revealed cs budget).map (Cubic.move dx dy))
      (1000 ≤ rt.reveal)
  | .back .., some last =>
    (if 1000 ≤ rt.reveal then body ++ arrowhead rt.key L.strokes.edge dx dy last else body, cache)
  | _, _ => (body, cache)

/-- A region's bracket: a frame in the rule's tone around its items, and its name in the label
face above its top left corner. -/
def regionCalls (L : Look) (dx dy : Int) (r : Region) : List (Keyed Call) :=
  (if L.strokes.radius = 0 then [⟨r.key, .frame .rule (dx + r.x) (dy + r.y) r.w r.h L.strokes.frame⟩]
   else [⟨r.key, .shape .rule 1000 (Grow.ring (1000 * (dx + r.x)) (1000 * (dy + r.y)) (1000 * r.w) (1000 * r.h)
     (2 * (L.strokes.radius : Int)) (1000 * (L.strokes.frame : Int)))⟩]) ++
    textAt r.key .label (dx + r.x + CELL) (dy + r.y + BASE) r.name (r.w - 2 * CELL)

/-- A mark's calls: a bar is a fill of the ink, centred on its height; a diamond, four straight
strokes. -/
def markCalls (L : Look) (dx dy : Int) : FlowMark → List (Keyed Call)
  | .bar k x0 x1 y =>
    if L.strokes.radius = 0 then [⟨k, .fill .ink 1000 (dx + x0) (barTop (dy + y)) (x1 - x0) BAR⟩]
    else [⟨k, .shape .ink 1000 [Grow.roundRect (1000 * (dx + x0)) (1000 * (barTop (dy + y))) (1000 * (x1 - x0))
      (1000 * BAR) (500 * BAR)]⟩]
  | .diamond k x y =>
    let c := (dx + x, dy + y)
    let n := (c.1, c.2 - DIAMOND)
    let e := (c.1 + DIAMOND, c.2)
    let s := (c.1, c.2 + DIAMOND)
    let w := (c.1 - DIAMOND, c.2)
    [n, e, s, w].zip [e, s, w, n] |>.map fun (a, b) => ⟨k, .curve .ink (straight a b) L.strokes.edge⟩

/-- **A laid-out graph as calls, on a stroke cache**, with its top left at `(dx, dy)`: the regions
behind, then the routes, then the marks and the boxes over them. The places are read by the
index, built once. -/
def callsCached (L : Look) (l : Laid) (dx dy : Int) (cache : StrokeCache) :
    List (Keyed Call) × StrokeCache :=
  let ix := Ix.of l
  let (routes, cache) := l.routes.toList.foldl (fun (acc : List (List (Keyed Call)) × StrokeCache) rt =>
    let (cs, c) := routeCalls L ix.find ix.onBar l.routeWidth dx dy acc.2 rt
    (cs :: acc.1, c)) ([], cache)
  (l.regions.toList.flatMap (regionCalls L dx dy) ++ routes.reverse.flatten ++
    l.marks.toList.flatMap (markCalls L dx dy) ++
    l.placed.toList.flatMap (fun p => match p.node with
      | some n => boxCalls L dx dy p n
      | none => []), cache)

/-- **A laid-out graph as calls**, with its top left at `(dx, dy)`: the drawing on a fresh stroke
cache. -/
def calls (L : Look) (l : Laid) (dx dy : Int) : List (Keyed Call) := (callsCached L l dx dy {}).1

/-- No two boxes share a pixel: a finite check of a layout. -/
def boxesApart (l : Laid) : Bool :=
  let boxes := l.placed.toList.filter (·.node.isSome)
  let apart (p q : Placed) : Bool :=
    p.x + p.w ≤ q.x || q.x + q.w ≤ p.x || p.y + ROWH * BOXROWS ≤ q.y || q.y + ROWH * BOXROWS ≤ p.y
  let rec go : List Placed → Bool
    | [] => true
    | p :: rest => rest.all (apart p) && go rest
  go boxes

/-- One downward segment descends when both keys resolve and the target top is at or below
its source bottom. A point has no height. Lookup retains the first matching key. -/
def segmentDescends (l : Laid) (u v : Key) : Bool :=
  match l.find u, l.find v with
  | some a, some b => a.y + (if a.node.isSome then ROWH * BOXROWS else 0) ≤ b.y
  | _, _ => false

/-- Check every adjacent pair of a downward route. Empty and singleton routes have no segment
and pass. This finite geometry check states no route-shape or dimension judgment. -/
def downRouteDescends (l : Laid) (ks : List Key) : Bool :=
  (ks.zip ks.tail).all fun pair => l.segmentDescends pair.1 pair.2

/-- The finite downward-route check accepts exactly when every adjacent pair descends.
This named tool law serves R14 and decisions row 336(8). Its consumer is `edgesDescend_down_pairs`.
Placement: `docs/research/2026-10-10-live-graph-support/routes/PLAN.md`. -/
theorem downRouteDescends_iff (l : Laid) (ks : List Key) :
    l.downRouteDescends ks = true ↔
      ∀ pair ∈ ks.zip ks.tail, l.segmentDescends pair.1 pair.2 = true :=
  List.all_eq_true

/-- Every adjacent segment drawn down descends, with both endpoint keys resolved.
Back and loop routes pass this downward-only finite check. -/
def edgesDescend (l : Laid) : Bool :=
  l.routes.toList.all fun
    | .down _ ks _ _ => l.downRouteDescends ks
    | _ => true

/-- A passing layout check checks every adjacent pair of each downward route.
This named tool law serves R14. The view driver's `graph-edges-descend` result consumes the check.
Placement: `docs/research/2026-10-10-live-graph-support/routes/PLAN.md`. -/
theorem edgesDescend_down_pairs (l : Laid) (checked : l.edgesDescend = true)
    (key : Key) (ks : List Key) (reveal share : Nat)
    (member : Route.down key ks reveal share ∈ l.routes.toList) :
    ∀ pair ∈ ks.zip ks.tail, l.segmentDescends pair.1 pair.2 = true := by
  have route := List.all_eq_true.mp checked (.down key ks reveal share) member
  exact (downRouteDescends_iff l ks).mp route

/-- Every dimension of a layout is a size, and every place is inside the picture: the picture's
width and height, each item's width and each region's width and height are at least zero, and each
item stands at or right of the left edge and at or below the top. A finite check of a layout. -/
def dimsValid (l : Laid) : Bool :=
  decide (0 ≤ l.width) && decide (0 ≤ l.height) &&
    l.placed.toList.all (fun p => decide (0 ≤ p.w) && decide (0 ≤ p.x) && decide (0 ≤ p.y)) &&
    l.regions.toList.all fun r => decide (0 ≤ r.w) && decide (0 ≤ r.h)

end Laid

end Tools.View
