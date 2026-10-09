import Tools.View.Place
import Tools.View.Organic

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
deriving Repr

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
deriving Repr

/-- A route: a forward edge through its items, from its source to its target; a back edge, with
its source, its target and its lane at the right; or an edge from a node to itself. Each is drawn
from its source as far as its reveal, per mille; 1000 at rest. A forward edge carries its share of
the work, in millionths, which sets its width by da Vinci's rule (`Tools.View.Grow.split`). -/
inductive Route where
  | down (key : Key) (items : List Key) (reveal : Nat := 1000) (share : Nat := 1000000)
  | back (key : Key) (src dst : Key) (lane : Nat) (reveal : Nat := 1000)
  | loop (key : Key) (node : Key) (reveal : Nat := 1000)
deriving Repr

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
deriving Repr

/-- A mark of a program's flow, in the notation of UML's activity diagrams: a bar where branches
that all run part or meet, across `[x0, x1)` at the height `y`; a diamond where alternatives part
or meet, centred at `(x, y)`. -/
inductive FlowMark where
  | bar (key : Key) (x0 x1 y : Int)
  | diamond (key : Key) (x y : Int)
deriving Repr

/-- A laid-out graph: its placed items, its routes, its regions and its marks, and its size in
logical pixels. -/
structure Laid where
  placed : Array Placed := #[]
  routes : Array Route := #[]
  width : Int := 0
  height : Int := 0
  regions : Array Region := #[]
  marks : Array FlowMark := #[]
deriving Repr


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

/-- The position of a key in a rank's order. -/
def posIn (order : List Key) (k : Key) : Nat := order.findIdx (· == k)

/-- Order one rank by the barycentre of each item's neighbours in the rank beside it; an item
with none keeps its place. The sort is stable, so ties keep the order before. Barycentres are
compared as fractions, by cross products. -/
def reorder (order beside : List Key) (neighbours : Key → List Key) : List Key :=
  let bary (k : Key) : Nat × Nat :=
    let ns := (neighbours k).filter beside.contains
    if ns.isEmpty then (2 * posIn order k, 2)
    else (ns.foldl (fun s n => s + 2 * posIn beside n) 0, 2 * ns.length)
  order.mergeSort fun a b =>
    let (sa, ca) := bary a
    let (sb, cb) := bary b
    sa * cb ≤ sb * ca

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
  { placed := placed.toArray, routes := routes.toArray,
    width := CELL * (widest + (if backs.isEmpty then 0 else GAP + 2 * backs.length)),
    height := if ranksN == 0 then 0 else ROWH * LEVEL * (ranksN - 1) + ROWH * BOXROWS }

end Graph

/-! ## The drawing -/

namespace Laid

/-- The placed item with key `k`. -/
def find (l : Laid) (k : Key) : Option Placed := l.placed.find? (·.key == k)

/-- A box, grown about its centre as far as its `grow`: its ground, its band when lit, its frame;
its two lines and its pointer box once it has grown whole. -/
def boxCalls (L : Look) (dx dy : Int) (p : Placed) (n : GNode) : List (Keyed Call) :=
  if p.grow = 0 then [] else
  let h := ROWH * BOXROWS
  let w' := p.w * p.grow / 1000
  let h' := h * p.grow / 1000
  let x := dx + p.x + (p.w - w') / 2
  let y := dy + p.y + (h - h') / 2
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
def exitAt (p : Placed) : Pt := (middle p, p.y + (if p.node.isSome then ROWH * BOXROWS else 0))

/-- Where an edge enters an item from above: the middle of its top. -/
def entryAt (p : Placed) : Pt := (middle p, p.y)

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
drop off a box's right side. -/
def segments (L : Look) (l : Laid) : Route → List Cubic
  | .down _ ks _ _ =>
    let ps := ks.filterMap l.find
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
    match l.find s, l.find d with
    | some a, some b =>
      let lx := l.width - CELL * (2 * lane + 1)
      -- a box's side at its middle row; a point has no height, and is its own side
      let side (p : Placed) (rise : Int) : Pt :=
        if p.node.isSome then (p.x + p.w, p.y + ROWH - rise) else (p.x + 2 * CELL, p.y)
      let p : Pt := side a 0
      let q : Pt := side b BACK_RISE
      -- controls a third past the lane, so the arc's widest point reaches the lane
      let cx := lx + (lx - max p.1 q.1) / 3
      [⟨p, (cx, p.2), (cx, q.2), q⟩]
    | _, _ => []
  | .loop _ k _ =>
    match l.find k with
    | some a =>
      let x := a.x + a.w
      let y := a.y + ROWH
      [⟨(x, y - LOOP_HALF), (x + 2 * LOOP_REACH, y - 2 * LOOP_HALF),
        (x + 2 * LOOP_REACH, y + 2 * LOOP_HALF), (x, y + LOOP_HALF)⟩]
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

/-- **A forward edge as an organic stroke** (`Tools.View.Grow`): its width the trunk's times its
share of the work, never finer than the look's finest line; its edges moved by the noise its key
seeds, inside their band; a collar where it leaves a box or a bar, and, once it is whole, where it
meets one. While it grows, its tip narrows. -/
def organicCalls (l : Laid) (L : Look) (key : Key) (ks : List Key) (share : Nat)
    (cs : List Cubic) (whole : Bool) : List (Keyed Call) :=
  let o := L.organic
  let w : Int := max (o.fine : Int) ((o.trunk : Int) * share / 1000000)
  let R : Int := (o.flare : Int) * w / max 1 (o.trunk : Int)
  -- the surface a line meets: a box's edge, at the line's end; a bar's edge, half its thickness away
  let surface (k : Key) : Option Int := (l.find k).bind fun p =>
    if p.node.isSome then some 0 else if l.onBar p then some (500 * BAR) else none
  let body := Grow.stroke (Grow.seedOf key) o w cs (!whole)
  let start := match cs.head?, ks.head?.bind surface with
    | some c, some off => [Grow.collar (1000 * c.p0.1) (1000 * c.p0.2 + off) w R true]
    | _, _ => []
  let finish := match whole, cs.getLast?, ks.getLast?.bind surface with
    | true, some c, some off => [Grow.collar (1000 * c.p3.1) (1000 * c.p3.2 - off) w R false]
    | _, _, _ => []
  if body.isEmpty then [] else
    ([body] ++ start ++ finish).map fun path => ⟨key, .shape .ink 1000 [path]⟩

/-- A route's calls: its segments, drawn as far as its reveal, at the look's weight of an edge, or,
for a forward edge in a look with a trunk, as an organic stroke; an arc in a lane, drawn whole,
ends in an arrowhead. -/
def routeCalls (L : Look) (l : Laid) (dx dy : Int) (rt : Route) : List (Keyed Call) :=
  let cs := l.segments L rt
  let budget : Int := (cs.map (·.size)).foldl (· + ·) 0 * rt.reveal / 1000
  let body := drawn rt.key L.strokes.edge dx dy cs budget
  match rt, cs.getLast? with
  | .down key ks _ share, _ =>
    if L.organic.trunk = 0 then body
    else l.organicCalls L key ks share ((revealed cs budget).map (Cubic.move dx dy)) (1000 ≤ rt.reveal)
  | .back .., some last => if 1000 ≤ rt.reveal then body ++ arrowhead rt.key L.strokes.edge dx dy last else body
  | _, _ => body

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
    if L.strokes.radius = 0 then [⟨k, .fill .ink 1000 (dx + x0) (dy + y - BAR / 2) (x1 - x0) BAR⟩]
    else [⟨k, .shape .ink 1000 [Grow.roundRect (1000 * (dx + x0)) (1000 * (dy + y - BAR / 2)) (1000 * (x1 - x0))
      (1000 * BAR) (500 * BAR)]⟩]
  | .diamond k x y =>
    let c := (dx + x, dy + y)
    let n := (c.1, c.2 - DIAMOND)
    let e := (c.1 + DIAMOND, c.2)
    let s := (c.1, c.2 + DIAMOND)
    let w := (c.1 - DIAMOND, c.2)
    [n, e, s, w].zip [e, s, w, n] |>.map fun (a, b) => ⟨k, .curve .ink (straight a b) L.strokes.edge⟩

/-- **A laid-out graph as calls**, with its top left at `(dx, dy)`: the regions behind, then the
routes, then the marks and the boxes over them. -/
def calls (L : Look) (l : Laid) (dx dy : Int) : List (Keyed Call) :=
  l.regions.toList.flatMap (regionCalls L dx dy) ++
  l.routes.toList.flatMap (l.routeCalls L dx dy) ++
  l.marks.toList.flatMap (markCalls L dx dy) ++
    l.placed.toList.flatMap fun p => match p.node with
      | some n => boxCalls L dx dy p n
      | none => []

/-- No two boxes share a pixel: a finite check of a layout. -/
def boxesApart (l : Laid) : Bool :=
  let boxes := l.placed.toList.filter (·.node.isSome)
  let apart (p q : Placed) : Bool :=
    p.x + p.w ≤ q.x || q.x + q.w ≤ p.x || p.y + ROWH * BOXROWS ≤ q.y || q.y + ROWH * BOXROWS ≤ p.y
  let rec go : List Placed → Bool
    | [] => true
    | p :: rest => rest.all (apart p) && go rest
  go boxes

/-- Every edge drawn down descends: its target's top stands at or below its source's bottom (a
point has no height). A finite check of a layout; the program graph's law is planned
(`docs/research/2026-10-09-program-graph-design.md`, D3). -/
def edgesDescend (l : Laid) : Bool :=
  let bottom (p : Placed) : Int := p.y + (if p.node.isSome then ROWH * BOXROWS else 0)
  l.routes.toList.all fun
    | .down _ [u, v] _ _ =>
      match l.find u, l.find v with
      | some a, some b => bottom a ≤ b.y
      | _, _ => false
    | _ => true

/-- Every dimension of a layout is a size, and every place is inside the picture: the picture's
width and height, each item's width and each region's width and height are at least zero, and each
item stands at or right of the left edge and at or below the top. A finite check of a layout. -/
def dimsValid (l : Laid) : Bool :=
  decide (0 ≤ l.width) && decide (0 ≤ l.height) &&
    l.placed.toList.all (fun p => decide (0 ≤ p.w) && decide (0 ≤ p.x) && decide (0 ≤ p.y)) &&
    l.regions.toList.all fun r => decide (0 ≤ r.w) && decide (0 ≤ r.h)

end Laid

end Tools.View
