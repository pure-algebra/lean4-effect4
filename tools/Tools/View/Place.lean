import Std.Data.HashMap
import Tools.View.Grid

/-!
# Places across: Brandes and Köpf's coordinates, then a law of separation

Where each item of a layered graph stands across its rank, given the order of every rank
(`Tools.View.Graph.orders`). It follows Brandes and Köpf, "Fast and Simple Horizontal Coordinate
Assignment" (2001), the method of ELK, OGDF and dagre, in four steps:

1. **Alignment.** Rank by rank, each item is aligned with a median of its neighbours in the rank
   before, left to right, never crossing an alignment already made. An edge between two points
   (a long edge's run) is kept straight first: an edge that crosses one is not aligned. Aligned
   items form a block, and a block stands in one column.
2. **Compaction.** Each block stands as far left as its neighbours in every rank allow: the
   longest path through the blocks, each rank's neighbours apart by their half widths and a gap.
3. **Four ways.** Steps 1 and 2 run down and up, from the left and from the right (by mirror),
   which gives four candidate places for each item.
4. **Balance.** Each candidate is shifted to the narrowest one's edge, and an item stands at the
   mean of its two middle candidates.

The paper's classes, which pull blocks of one class toward each other, are left out: compaction
is one class. A last pass, `spread`, puts each rank's items apart from left to right, so that no
rounding or balance can make two items share a cell (`spread_apart`). Places are centres in half
cells, so an item of an odd width stands on whole cells.
-/

namespace Tools.View.Place

open Std

/-- A key of an item. -/
abbrev Key := String

/-- The positions of the items within their ranks. -/
def positions (ranks : List (List Key)) : HashMap Key Nat :=
  ranks.foldl (fun m r => r.zipIdx.foldl (fun m (k, i) => m.insert k i) m) {}

/-- The lower and upper medians of a sorted list, once each. -/
def medians (ns : List Key) : List Key :=
  let d := ns.length
  if d == 0 then [] else
  let lo := ns.getD ((d - 1) / 2) ""
  let hi := ns.getD (d / 2) ""
  if lo == hi then [lo] else [lo, hi]

/-- **The alignment**: each item's root, the first item of its block. Ranks are taken in the
given order; `nbrs` gives an item's neighbours in the rank before; `marked` an edge that must not
be aligned. -/
def roots (ranks : List (List Key)) (nbrs : Key → List Key) (marked : Key → Key → Bool) :
    HashMap Key Key :=
  let pos := positions ranks
  let init : HashMap Key Key := ranks.foldl (fun m r => r.foldl (fun m k => m.insert k k) m) {}
  (ranks.zip ranks.tail).foldl (fun root (before, here) =>
    (here.foldl (fun (acc : HashMap Key Key × Int) v =>
      let ns := ((nbrs v).filter before.contains).mergeSort fun a b => decide (pos.getD a 0 ≤ pos.getD b 0)
      let pick := (medians ns).find? fun m => !marked m v && acc.2 < (pos.getD m 0 : Int)
      match pick with
      | some m => (acc.1.insert v (acc.1.getD m m), pos.getD m 0)
      | none => acc) (root, -1)).1) init

/-- The distance between the centres of two neighbours in half cells: their half widths and a
gap, each doubled. -/
def sep (width : Key → Nat) (u v : Key) : Int := width u + width v + 2 * GAP

/-- **The compaction**: each block as far left as its neighbours allow, as the longest path through
the blocks. A pass relaxes every pair of neighbours once; as many passes as blocks reach the
longest path, since blocks never cross. -/
def compact (ranks : List (List Key)) (width : Key → Nat) (root : HashMap Key Key) : HashMap Key Int :=
  let cs : List (Key × Key × Int) := ranks.flatMap fun r =>
    (r.zip r.tail).map fun (u, v) => (root.getD u u, root.getD v v, sep width u v)
  let blocks := (ranks.flatten.map fun k => root.getD k k).eraseDups
  let pass (x : HashMap Key Int) : HashMap Key Int :=
    cs.foldl (fun x (a, b, s) => if x.getD b 0 < x.getD a 0 + s then x.insert b (x.getD a 0 + s) else x) x
  let x := (List.range (blocks.length + 1)).foldl (fun x _ => pass x) (blocks.foldl (fun m b => m.insert b 0) {})
  ranks.flatten.foldl (fun m k => m.insert k (x.getD (root.getD k k) 0)) {}

/-- One way: aligned along `ranks` with the neighbours `nbrs`, packed from the left. -/
def oneWay (ranks : List (List Key)) (width : Key → Nat) (nbrs : Key → List Key)
    (marked : Key → Key → Bool) : HashMap Key Int :=
  compact ranks width (roots ranks nbrs marked)

/-- The same way from the right: each rank mirrored, packed, and mirrored back. -/
def mirrored (ranks : List (List Key)) (width : Key → Nat) (nbrs : Key → List Key)
    (marked : Key → Key → Bool) : HashMap Key Int :=
  (oneWay (ranks.map List.reverse) width nbrs marked).fold (fun m k x => m.insert k (-x)) {}

/-- The extent of a candidate: its least left edge and its greatest right edge, in half cells. -/
def extent (keys : List Key) (width : Key → Nat) (x : HashMap Key Int) : Int × Int :=
  keys.foldl (fun (lo, hi) k => (min lo (x.getD k 0 - width k), max hi (x.getD k 0 + width k)))
    ((x.getD (keys.headD "") 0) - width (keys.headD ""), (x.getD (keys.headD "") 0) + width (keys.headD ""))

/-- A candidate shifted by `d`. -/
def shift (d : Int) (x : HashMap Key Int) : HashMap Key Int := x.fold (fun m k v => m.insert k (v + d)) {}

/-- The edges that cross a run of a long edge, between ranks `i` and `i + 1`: Brandes and Köpf's
conflicts of the first type. Both orders of a pair are marked. -/
def conflicts (ranks : List (List Key)) (links : List (Key × Key)) (isPoint : Key → Bool) :
    List (Key × Key) :=
  let pos := positions ranks
  let p (k : Key) : Int := pos.getD k 0
  let inner := links.filter fun (a, b) => isPoint a && isPoint b
  let outer := links.filter fun (a, b) => !(isPoint a && isPoint b)
  outer.filter fun (a, b) => inner.any fun (c, d) =>
    ranks.any (fun r => r.contains a && r.contains c) &&
      ((p a < p c && p d < p b) || (p c < p a && p b < p d))

/-- **Separation**: each centre at least `sep` right of the one before it, keeping it where it is
when it already is. -/
def spread (width : Key → Nat) : Option (Key × Int) → List (Key × Int) → List (Key × Int)
  | _, [] => []
  | none, (k, x) :: rest => (k, x) :: spread width (some (k, x)) rest
  | some (u, xu), (k, x) :: rest =>
    let x' := max x (xu + sep width u k)
    (k, x') :: spread width (some (k, x')) rest

/-- Each centre of a list stands at least `sep` right of the one before it. -/
def Apart (width : Key → Nat) : Option (Key × Int) → List (Key × Int) → Prop
  | _, [] => True
  | none, (k, x) :: rest => Apart width (some (k, x)) rest
  | some (u, xu), (k, x) :: rest => xu + sep width u k ≤ x ∧ Apart width (some (k, x)) rest

/-- **The law of separation**: whatever the candidates, `spread` puts every item of a rank apart
from the one before it by their half widths and a gap. So two items of one rank never share a
cell. -/
theorem spread_apart (width : Key → Nat) :
    ∀ (prev : Option (Key × Int)) (xs : List (Key × Int)), Apart width prev (spread width prev xs)
  | _, [] => trivial
  | none, (k, x) :: rest => spread_apart width (some (k, x)) rest
  | some _, _ :: rest => ⟨Int.le_max_right _ _, spread_apart width _ rest⟩

/-- **The centres** of every item, in half cells, the least left edge at zero: four ways, balanced,
then spread. `ups` and `downs` give an item's neighbours in the ranks above and below. -/
def centres (ranks : List (List Key)) (width : Key → Nat) (ups downs : Key → List Key)
    (links : List (Key × Key)) (isPoint : Key → Bool) : HashMap Key Int :=
  let keys := ranks.flatten
  if keys.isEmpty then {} else
  let cs := conflicts ranks links isPoint
  let marked (a b : Key) : Bool := cs.contains (a, b) || cs.contains (b, a)
  let ways : List (HashMap Key Int × Bool) :=
    [(oneWay ranks width ups marked, true), (mirrored ranks width ups marked, false),
      (oneWay ranks.reverse width downs marked, true), (mirrored ranks.reverse width downs marked, false)]
  let ext := ways.map fun (x, _) => extent keys width x
  let narrowest := (ext.zip ways).foldl (fun best (e, w) =>
    if e.2 - e.1 < best.1.2 - best.1.1 then (e, w) else best) (ext.headD (0, 0), ways.headD ({}, true))
  let (lo, hi) := narrowest.1
  let aligned := (ext.zip ways).map fun ((l, h), (x, fromLeft)) => shift (if fromLeft then lo - l else hi - h) x
  let balanced : HashMap Key Int := keys.foldl (fun m k =>
    let vs := (aligned.map fun x => x.getD k 0).mergeSort fun a b => decide (a ≤ b)
    m.insert k ((vs.getD 1 0 + vs.getD 2 0) / 2)) {}
  let spreadRank (m : HashMap Key Int) (r : List Key) : HashMap Key Int :=
    (spread width none (r.map fun k => (k, balanced.getD k 0))).foldl (fun m (k, x) => m.insert k x) m
  let spreadAll := ranks.foldl spreadRank {}
  let least := keys.foldl (fun m k => min m (spreadAll.getD k 0 - width k)) (spreadAll.getD keys.head! 0 - width keys.head!)
  shift (-least) spreadAll

end Tools.View.Place
