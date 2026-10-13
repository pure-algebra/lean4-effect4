import Tools.View.Organic
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Tools.View.Living.Soft — membranes as the contours of a soft field

A cell's membrane is where a field falls to a level. Wyvill, McPheeters and Wyvill's soft
objects ("Data structure for soft objects", *The Visual Computer* 2, 1986) give each source a
field that is one at the source and falls to zero at its radius of influence `R`, as a polynomial
in the square of the distance, so no square root is taken:

  `C(s) = 1 − (4/9) s³ + (17/9) s² − (22/9) s`, with `s = r² / R²` and `C = 0` past `R`.

It is one at the source, zero at `R` with a zero slope, and one half at `R / 2` (the conditions
of the SIGGRAPH HyperGraph notes on blobby objects; the coefficients are recalled and checked by
the guards below). Fields add, so two sources near each other merge with a smooth neck: a
channel meets its vessel in an organic collar by construction, and a vessel swells where its
contents press.

* `Source`: a segment with a radius of influence at each end (a point when its ends meet); a
  channel is a tapered segment, a droplet a point.
* `Grid.of`: the field sampled on a grid, each source added only inside its own box: the work is
  the sum of the sources' areas, not the grid times the sources.
* `Grid.contours level`: marching squares (Lorensen and Cline's marching cubes, in two
  dimensions): the closed polylines where the field crosses `level`, each crossing placed on its
  edge by linear interpolation, a saddle resolved by the cell's centre.
* `smooth`: a closed polyline thinned and drawn through by Catmull-Rom's spline
  (`Grow.through`), as cubic segments in thousandths of a pixel, ready for `Call.shape`.

Every line drawn from the field is a contour of it at one width (`Grid.lines`): the contour and
its copy moved a fixed width inward, filled by the even-odd rule. The membrane is the contour at
the body's level, and the lamellae inside it are the contours at higher levels, like the layers of
cartilage, so every line of the body comes from the one structure.
Everything is whole numbers: pixels for places, thousandths for the field and the points.
-/

namespace Tools.View.Living.Soft
open Tools.View

/-- **A source of the field**: a segment from `a` to `b` in logical pixels, its radius of
influence growing from `ra` at `a` to `rb` at `b`, and its weight in thousandths. -/
structure Source where
  ax : Int
  ay : Int
  bx : Int
  by_ : Int
  ra : Nat
  rb : Nat
  weight : Nat := 1000
deriving Repr

/-- A point source. -/
def Source.point (x y : Int) (r : Nat) (weight : Nat := 1000) : Source := ⟨x, y, x, y, r, r, weight⟩

/-- A segment of one radius. -/
def Source.segment (ax ay bx by_ : Int) (r : Nat) (weight : Nat := 1000) : Source :=
  ⟨ax, ay, bx, by_, r, r, weight⟩

/-- **The soft-object kernel** in thousandths, at `s = r² / R²` in thousandths: one at the
source, zero from `R` on. -/
def kernel (s : Int) : Int :=
  if s ≥ 1000 then 0 else
  (9000000000 - 4 * s * s * s + 17000 * s * s - 22000000 * s) / 9000000

-- one at the source, one half at half the radius, zero at the radius
#guard kernel 0 == 1000
#guard kernel 250 == 500
#guard kernel 1000 == 0

/-- The field of one source at a point, in thousandths: the nearest point of the segment, the
radius there, then the kernel. -/
def Source.at (src : Source) (px py : Int) : Int :=
  let dx := src.bx - src.ax
  let dy := src.by_ - src.ay
  let len2 := dx * dx + dy * dy
  let t : Int := if len2 == 0 then 0 else max 0 (min 1000 (((px - src.ax) * dx + (py - src.ay) * dy) * 1000 / len2))
  let qx := src.ax * 1000 + dx * t
  let qy := src.ay * 1000 + dy * t
  let ex := px * 1000 - qx
  let ey := py * 1000 - qy
  let r : Int := (src.ra : Int) * 1000 + ((src.rb : Int) - src.ra) * t
  if r ≤ 0 then 0 else
  kernel ((ex * ex + ey * ey) * 1000 / (r * r)) * src.weight / 1000

/-- **A field sampled on a grid**: `nx` by `ny` samples, `step` pixels apart, the first at
`(x0, y0)`; row by row. -/
structure Grid where
  x0 : Int
  y0 : Int
  step : Nat
  nx : Nat
  ny : Nat
  values : Array Int

/-- The sample at a column and a row; zero outside. -/
def Grid.get (g : Grid) (i j : Nat) : Int := if i < g.nx && j < g.ny then g.values.getD (j * g.nx + i) 0 else 0

/-- **The field of some sources on a grid**, each added only inside its own box. -/
def Grid.of (x0 y0 : Int) (step nx ny : Nat) (sources : List Source) : Grid := Id.run do
  let mut vs : Array Int := Array.replicate (nx * ny) 0
  let st : Int := step
  for src in sources do
    let reach : Int := max src.ra src.rb
    let lo (a b x0 : Int) : Nat := ((min a b - reach - x0) / st).toNat
    let hi (a b x0 : Int) (n : Nat) : Nat := min n ((max a b + reach - x0) / st + 2).toNat
    for j in [lo src.ay src.by_ y0 : hi src.ay src.by_ y0 ny] do
      for i in [lo src.ax src.bx x0 : hi src.ax src.bx x0 nx] do
        let v := src.at (x0 + i * st) (y0 + j * st)
        if v != 0 then vs := vs.modify (j * nx + i) (· + v)
  return ⟨x0, y0, step, nx, ny, vs⟩

/-- The key of a grid edge: the horizontal edge from sample `(i, j)` to its right is `2k`, the
vertical edge from it downward `2k + 1`, where `k` is the sample's index. -/
def edgeKey (g : Grid) (i j : Nat) (vertical : Bool) : Nat := 2 * (j * g.nx + i) + (if vertical then 1 else 0)

/-- The point where the field crosses `level` on an edge, in thousandths of a pixel. -/
def Grid.crossing (g : Grid) (level : Int) (key : Nat) : Int × Int :=
  let k := key / 2
  let i := k % g.nx
  let j := k / g.nx
  let vertical := key % 2 == 1
  let (i', j') := if vertical then (i, j + 1) else (i + 1, j)
  let va := g.get i j
  let vb := g.get i' j'
  let st : Int := g.step
  let t : Int := if vb == va then 500 else (level - va) * 1000 / (vb - va)
  let ax := (g.x0 + i * st) * 1000
  let ay := (g.y0 + j * st) * 1000
  if vertical then (ax, ay + st * t) else (ax + st * t, ay)

/-- The segments of one cell by marching squares, as pairs of edge keys. -/
def Grid.cell (g : Grid) (level : Int) (i j : Nat) : List (Nat × Nat) :=
  let a := g.get i j
  let b := g.get (i + 1) j
  let c := g.get (i + 1) (j + 1)
  let d := g.get i (j + 1)
  let bit (v : Int) (w : Nat) : Nat := if v ≥ level then w else 0
  let top := edgeKey g i j false
  let right := edgeKey g (i + 1) j true
  let bottom := edgeKey g i (j + 1) false
  let left := edgeKey g i j true
  let centre := (a + b + c + d) / 4 ≥ level
  match bit a 1 + bit b 2 + bit c 4 + bit d 8 with
  | 1 | 14 => [(left, top)]
  | 2 | 13 => [(top, right)]
  | 3 | 12 => [(left, right)]
  | 4 | 11 => [(right, bottom)]
  | 6 | 9 => [(top, bottom)]
  | 7 | 8 => [(left, bottom)]
  | 5 => if centre then [(top, right), (bottom, left)] else [(left, top), (right, bottom)]
  | 10 => if centre then [(left, top), (right, bottom)] else [(top, right), (bottom, left)]
  | _ => []

/-- **The contours of the field at a level**: closed loops of edge keys, each crossing met twice,
so a walk from any crossing comes back to it. The grid's border must be below the level. -/
def Grid.loops (g : Grid) (level : Int) : List (List Nat) := Id.run do
  let mut adj : Std.HashMap Nat (List Nat) := {}
  for j in [0 : g.ny - 1] do
    for i in [0 : g.nx - 1] do
      for (p, q) in g.cell level i j do
        adj := adj.insert p (q :: adj.getD p [])
        adj := adj.insert q (p :: adj.getD q [])
  let mut seen : Std.HashSet Nat := {}
  let mut out : List (List Nat) := []
  for (start, _) in adj.toList do
    if seen.contains start then continue
    let mut loop : Array Nat := #[start]
    seen := seen.insert start
    let mut prev := start
    let mut cur := (adj.getD start []).headD start
    for _ in [0 : adj.size] do
      if cur == start || seen.contains cur then break
      loop := loop.push cur
      seen := seen.insert cur
      let next := (adj.getD cur []).filter (· != prev)
      prev := cur
      cur := next.headD start
    out := loop.toList :: out
  return out

/-- A closed polyline thinned: every `keep`-th point. -/
def thin (keep : Nat) (pts : List (Int × Int)) : List (Int × Int) :=
  (pts.zipIdx.filter fun (_, i) => i % (max 1 keep) == 0).map (·.1)

/-- **A closed ring of points drawn smooth**: Catmull-Rom's spline through them, closed, as cubic
segments. A ring of fewer than three points draws nothing. -/
def closed (ring : List (Int × Int)) : List Cubic :=
  match ring with
  | a :: b :: _ :: _ =>
    let last := (ring.getLast?).getD a
    (Grow.throughFrom last (ring ++ [a, b])).take ring.length
  | _ => []

/-- A closed polyline thinned and drawn smooth. -/
def smooth (keep : Nat) (pts : List (Int × Int)) : List Cubic := closed (thin keep pts)

/-- **The contours of the field at a level**, smooth, as closed paths for `Call.shape`. -/
def Grid.paths (g : Grid) (level : Int) (keep : Nat := 3) : List (List Cubic) :=
  (g.loops level).filterMap fun loop =>
    let p := smooth keep (loop.map (g.crossing level))
    if p.isEmpty then none else some p

/-- **The field at a point** in thousandths of a pixel: the bilinear reading of the four samples
around it. -/
def Grid.sample (g : Grid) (x y : Int) : Int :=
  let st : Int := (g.step : Int) * 1000
  let fx := x - g.x0 * 1000
  let fy := y - g.y0 * 1000
  if fx < 0 || fy < 0 then 0 else
  let i := (fx / st).toNat
  let j := (fy / st).toNat
  let u := fx % st
  let v := fy % st
  let top := g.get i j * (st - u) + g.get (i + 1) j * u
  let bot := g.get i (j + 1) * (st - u) + g.get (i + 1) (j + 1) * u
  (top * (st - v) + bot * v) / (st * st)

/-- **A ring moved inward by `w`** thousandths of a pixel: each point along its normal, to the
side where the field is higher. -/
def Grid.inward (g : Grid) (w : Int) (pts : List (Int × Int)) : List (Int × Int) :=
  let arr := pts.toArray
  let n := arr.size
  (List.range n).map fun k =>
    let p := arr.getD k (0, 0)
    let a := arr.getD ((k + n - 1) % n) p
    let b := arr.getD ((k + 1) % n) p
    let tx := b.1 - a.1
    let ty := b.2 - a.2
    let len : Int := Grow.isqrt (tx * tx + ty * ty).toNat
    if len == 0 then p else
    let nx := -ty * w / len
    let ny := tx * w / len
    if g.sample (p.1 + nx) (p.2 + ny) ≥ g.sample (p.1 - nx) (p.2 - ny) then (p.1 + nx, p.2 + ny)
    else (p.1 - nx, p.2 - ny)

/-- **The contours at a level as lines of one width**: each loop thinned, its inner edge `w`
thousandths of a pixel inward, both drawn smooth. Filled by the even-odd rule, each loop is a
line of constant width along the contour, so every line of a picture drawn from one field reads
as one material. -/
def Grid.lines (g : Grid) (level : Int) (w : Int) (keep : Nat := 3) : List (List Cubic) :=
  (g.loops level).flatMap fun loop =>
    let pts := thin keep (loop.map (g.crossing level))
    if pts.length < 3 then [] else [closed pts, closed (g.inward w pts)]

end Tools.View.Living.Soft
