import Tools.View.Grid

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
   below, and packed left to right on the cell grid; the ranks are centred.
4. **Routes.** A forward edge runs down through the channel between two ranks: a stem, a bar, a
   stem. A back edge leaves its source's right side, climbs a lane of its own at the right, and
   enters its target's right side. An edge from a node to itself is a small loop off its right
   side, with no lane.

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
from its source as far as its reveal, per mille; 1000 at rest. -/
inductive Route where
  | down (key : Key) (items : List Key) (reveal : Nat := 1000)
  | back (key : Key) (src dst : Key) (lane : Nat) (reveal : Nat := 1000)
  | loop (key : Key) (node : Key) (reveal : Nat := 1000)
deriving Repr

namespace Route

/-- A route's key. -/
def key : Route → Key
  | .down k _ _ | .back k _ _ _ _ | .loop k _ _ => k

/-- A route's reveal. -/
def reveal : Route → Nat
  | .down _ _ r | .back _ _ _ _ r | .loop _ _ r => r

/-- A route with another reveal. -/
def withReveal (r : Nat) : Route → Route
  | .down k ks _ => .down k ks r
  | .back k s d lane _ => .back k s d lane r
  | .loop k n _ => .loop k n r

/-- A route keeps itself under its own reveal. -/
theorem withReveal_self (rt : Route) : rt.withReveal rt.reveal = rt := by
  cases rt <;> rfl

end Route

/-- A laid-out graph: its placed items and its routes, and its size in logical pixels. -/
structure Laid where
  placed : Array Placed := #[]
  routes : Array Route := #[]
  width : Int := 0
  height : Int := 0
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

/-- **The layout** of a graph: the ranks, the order of each rank, each item packed left to right
on the cell grid with each rank centred, the routes, and the lanes of the back edges. -/
def layout (g : Graph) : Laid :=
  let rk := ranks g
  let its := items g rk
  let width (k : Key) : Nat := ((its.find? (·.key == k)).map (·.width)).getD GAP
  let os := orders g rk
  let rankCells (o : List Key) : Nat := o.foldl (fun s k => s + width k) 0 + GAP * (o.length - 1)
  let widest := os.foldl (fun m o => max m (rankCells o)) 0
  let placed : List Placed := os.zipIdx.flatMap fun (o, r) =>
    let left := (widest - rankCells o) / 2
    (o.foldl (fun (acc : Nat × List Placed) k =>
      let node := (its.find? (·.key == k)).bind (·.node)
      (acc.1 + width k + GAP,
        acc.2 ++ [{ key := k, x := CELL * acc.1, y := ROWH * LEVEL * r, w := CELL * width k, node }])) (left, [])).2
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
def boxCalls (dx dy : Int) (p : Placed) (n : GNode) : List (Keyed Call) :=
  if p.grow = 0 then [] else
  let h := ROWH * BOXROWS
  let w' := p.w * p.grow / 1000
  let h' := h * p.grow / 1000
  let x := dx + p.x + (p.w - w') / 2
  let y := dy + p.y + (h - h') / 2
  let room : Int := p.w / CELL - 2
  [⟨p.key, .fill .ground 1000 x y w' h'⟩] ++
    (if n.lit then [⟨p.key, .fill .rule 500 x y w' h'⟩] else []) ++
    [⟨p.key, .frame .ink x y w' h' 1⟩] ++
    (if 1000 ≤ p.grow then
      cellsAt p.key (dx + p.x + CELL) (dy + p.y + BASE) n.line1 room ++
        cellsAt p.key (dx + p.x + CELL) (dy + p.y + ROWH + BASE) n.line2 room ++
        [⟨p.key, .hit (dx + p.x) (dy + p.y) p.w h⟩]
    else [])

/-- A point of a route, in the graph's own logical pixels. -/
abbrev Pt := Int × Int

/-- Where an edge leaves an item downward, and where one enters it from above: the middle of a
box's bottom or top; a point is a vertical pass through its rank. -/
def bottom (p : Placed) : Pt := (p.x + (if p.node.isSome then p.w / 2 else CELL), p.y + ROWH * BOXROWS)
def top (p : Placed) : Pt := (p.x + (if p.node.isSome then p.w / 2 else CELL), p.y)

/-- **A route as a path**: its corners from its source to its target. A forward route takes, at
each step, a stem down to the channel, a bar across it, and a stem down to the next item, and
passes through each point's rank. A back route leaves its source's right side, climbs its lane,
and enters its target's right side. A loop leaves a box's right side and comes back to it. -/
def points (l : Laid) : Route → List Pt
  | .down _ ks _ =>
    let ps := ks.filterMap l.find
    if ps.length != ks.length then [] else
    match ps with
    | [] => []
    | a :: rest =>
      (rest.foldl (fun (acc : List Pt × Placed) b =>
        let (ax, ay) := bottom acc.2
        let (bx, by_) := top b
        let bar := ay + (by_ - ay) / 2
        let through : List Pt := if b.node.isNone then [(bx, by_ + ROWH * BOXROWS)] else []
        (acc.1 ++ [(ax, bar), (bx, bar), (bx, by_)] ++ through, b)) ([bottom a], a)).1
  | .back _ s d lane _ =>
    match l.find s, l.find d with
    | some a, some b =>
      let lx := l.width - CELL * (2 * lane + 1)
      [(a.x + a.w, a.y + ROWH), (lx, a.y + ROWH), (lx, b.y + ROWH - BACK_RISE), (b.x + b.w, b.y + ROWH - BACK_RISE)]
    | _, _ => []
  | .loop _ k _ =>
    match l.find k with
    | some a =>
      let x := a.x + a.w
      let y := a.y + ROWH
      [(x, y - LOOP_HALF), (x + LOOP_REACH, y - LOOP_HALF), (x + LOOP_REACH, y + LOOP_HALF), (x, y + LOOP_HALF)]
    | none => []

/-- The length of one straight piece of a path. -/
def span (p q : Pt) : Int := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

/-- One straight piece, as a rule of one pixel from `p` toward `q`. -/
def piece (key : Key) (dx dy : Int) (p q : Pt) : Keyed Call :=
  if p.2 = q.2 then ⟨key, .hrule .ink (dx + min p.1 q.1) (dy + p.2) ((p.1 - q.1).natAbs + 1) 1⟩
  else ⟨key, .vrule .ink (dx + p.1) (dy + min p.2 q.2) ((p.2 - q.2).natAbs + 1) 1⟩

/-- The point `d` pixels from `p` toward `q`, along a straight piece. -/
def toward (p q : Pt) (d : Int) : Pt :=
  if p.2 = q.2 then (if p.1 ≤ q.1 then p.1 + d else p.1 - d, p.2)
  else (p.1, if p.2 ≤ q.2 then p.2 + d else p.2 - d)

/-- **A path drawn from its start for `budget` pixels**: each whole piece within the budget, then
the part of the next piece that the budget reaches. -/
def drawn (key : Key) (dx dy : Int) : List Pt → Int → List (Keyed Call)
  | p :: rest, budget =>
    match rest with
    | q :: _ =>
      if budget ≤ 0 then []
      else if span p q ≤ budget then piece key dx dy p q :: drawn key dx dy rest (budget - span p q)
      else [piece key dx dy p (toward p q budget)]
    | [] => []
  | [], _ => []

/-- A path's length: the sum of its pieces. -/
def length : List Pt → Int
  | p :: rest =>
    match rest with
    | q :: _ => span p q + length rest
    | [] => 0
  | [] => 0

/-- A route's calls: its path, drawn as far as its reveal. -/
def routeCalls (l : Laid) (dx dy : Int) (rt : Route) : List (Keyed Call) :=
  let pts := l.points rt
  drawn rt.key dx dy pts (length pts * rt.reveal / 1000)

/-- **A laid-out graph as calls**, with its top left at `(dx, dy)`: the routes first, then the
boxes over them. -/
def calls (l : Laid) (dx dy : Int) : List (Keyed Call) :=
  l.routes.toList.flatMap (l.routeCalls dx dy) ++
    l.placed.toList.flatMap fun p => match p.node with
      | some n => boxCalls dx dy p n
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

end Laid

end Tools.View
