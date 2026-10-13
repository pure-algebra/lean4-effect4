import Tools.View.Tube.Form
import Tools.View.Organic

/-!
# Tools.View.Tube.Outline — solid bodies: a tube's outline, a stretch of changing width, a rounded crotch

The owner's ruling of 2026-10-13 (decisions row 370): a tube is a **solid body**, filled in one
tone, and its outline is smooth everywhere, with no kink.

* **A body's outline** (`bodyCubics`): the tube's two parallels at half its width, joined by its
  caps, round where the tube is closed and cut square where it opens to the world. The parallel of
  an arc is an arc of the same turn and of a radius less or more by the distance (`Tube.offset`),
  so the outline of a body of one width is exact, and as smooth as its centreline: the bend law
  makes every piece meet the next on its tangent.
* **A stretch of changing width** (`patchCubics`): where a width changes along a tube (a swell
  round a unit carried, a reducer from a pipe to a wider vessel, a sleeve), the outline is a
  smooth curve through its points, its width eased by the smoothstep `u²(3 − 2u)`, whose slope is
  nothing at both ends. So the stretch meets the body on its tangent and adds no kink.
* **A rounded crotch** (`crotch`): where a branch leaves a body on its tangent and turns away, its
  inner edge leaves the body's edge at a narrow angle, a notch. A fillet of radius `FILLET` rounds
  it: the circle that touches the body's edge and the branch's edge, as a cast fitting is rounded.

Every curve is cubic Béziers, so a morph of a body samples its outline with the same commands at
every moment.
-/

namespace Tools.View.Tube
open Tools.View

/-- The normal at a heading, on the side a positive turn turns toward, at the scale `ONE`. -/
def normal (h : Int) : Int × Int := let (s, c) := sinCos h; (-s, c)

/-- A point moved `d` thousandths of a pixel along a unit vector at the scale `ONE`. -/
def along (p : Int × Int) (d : Int) (v : Int × Int) : Int × Int :=
  (p.1 + d * v.1 / ONE, p.2 + d * v.2 / ONE)

/-- **A tube's parallel** at the distance `d`, on the side a positive turn turns toward (the other
side for `d < 0`). The parallel of an arc is an arc of the same turn, `ℓ − d·θ` long, so it is
exact; a piece tighter than `d` has a parallel of no length. -/
def Tube.offset (t : Tube) (d : Int) : Tube :=
  let p := along (t.x, t.y) d (normal t.head)
  ⟨p.1, p.2, t.head, t.bore,
   t.pieces.map fun pc => ⟨((pc.len : Int) - d * pc.turn / 1000000).toNat, pc.turn⟩⟩

/-- A cubic run backwards. -/
def Cubic.rev (c : Cubic) : Cubic := ⟨c.p3, c.p2, c.p1, c.p0⟩

/-- A straight line as a cubic, so every segment of an outline is one kind. -/
def lineC (a b : Int × Int) : Cubic :=
  ⟨a, (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3),
   (a.1 + 2 * (b.1 - a.1) / 3, a.2 + 2 * (b.2 - a.2) / 3), b⟩

/-- The handle of a quarter circle as a cubic, in millionths of its radius. -/
def KAPPA : Int := 552285

/-- **A half circle** from `a` round the tip `e + r·d` to `b`, as two quarter cubics: the cap of an
end of radius `r` at `e`, heading `d`, its edges' ends `a` (start side) and `b`. -/
def capC (a b e : Int × Int) (r : Int) (d n : Int × Int) : List Cubic :=
  let k := r * KAPPA / 1000000
  let tip := along e r d
  [⟨a, along a k d, along tip (-k) n, tip⟩, ⟨tip, along tip k n, along b k d, b⟩]

/-- **A body's outline**, as one closed run of cubics: the parallel at `−w/2` from start to end,
the end's cap, the parallel at `w/2` back, the start's cap. A cap is round where the tube is
closed, and a straight cut where it opens to the world. -/
def bodyCubics (t : Tube) (w : Nat) (roundStart roundEnd : Bool) : List Cubic :=
  let r : Int := w / 2
  let left := (t.offset (-r)).cubics
  let right := ((t.offset r).cubics.map Cubic.rev).reverse
  match left.head?, left.getLast?, right.head?, right.getLast? with
  | some l0, some l1, some r0, some r1 =>
    let (e, he) := t.at t.length
    let endCap := if roundEnd then capC l1.p3 r0.p0 e r (dir he) (normal he) else [lineC l1.p3 r0.p0]
    let n0 := normal t.head
    let d0 := dir t.head
    let startCap :=
      if roundStart then capC r1.p3 l0.p0 (t.x, t.y) r (-d0.1, -d0.2) (-n0.1, -n0.2)
      else [lineC r1.p3 l0.p0]
    left ++ endCap ++ right ++ startCap
  | _, _, _, _ => []

/-! ## A stretch of changing width -/

/-- **The smoothstep** `u²(3 − 2u)` in thousandths: from nothing to one, its slope nothing at both
ends. -/
def smooth (u : Nat) : Nat := let v := min u 1000; v * v * (3000 - 2 * v) / 1000000

/-- **The width of a stretch** `u` along it, of `len`: from `w0` to `w1` by the smoothstep, and
`peak` more within it, eased in and out over `rise` at each end. A swell is a peak whose rise is
half the stretch; a sleeve is a peak with a short rise; a reducer is a change from `w0` to `w1`. -/
def stretchWidth (w0 w1 : Nat) (peak : Int) (rise len u : Nat) : Int :=
  let base : Int := (w0 : Int) + ((w1 : Int) - w0) * (smooth (if len = 0 then 0 else u * 1000 / len)) / 1000
  let ramp : Nat := if rise = 0 then 1000 else smooth (min u (len - u) * 1000 / rise)
  base + peak * ramp / 1000

/-- The points of a stretch taken. -/
def STRETCH : Nat := 12

/-- A run of cubics through points, each with its tangent: Catmull and Rom's spline, whose
neighbouring segments meet on one tangent. The ends' tangents are given. -/
def throughC (ps : List (Int × Int)) (m0 m1 : Int × Int) : List Cubic :=
  let n := ps.length
  let at_ (i : Nat) : Int × Int := ps.getD i (0, 0)
  let tan (i : Nat) : Int × Int :=
    if i = 0 then m0 else if i + 1 ≥ n then m1
    else ((at_ (i + 1)).1 - (at_ (i - 1)).1, (at_ (i + 1)).2 - (at_ (i - 1)).2)
  (List.range (n - 1)).map fun i =>
    let a := at_ i
    let b := at_ (i + 1)
    let ta := tan i
    let tb := tan (i + 1)
    ⟨a, (a.1 + ta.1 / 6, a.2 + ta.2 / 6), (b.1 - tb.1 / 6, b.2 - tb.2 / 6), b⟩

/-- **A stretch's outline**: the part of the tube from `s` along it, `len` long, its width from
`w0` to `w1` with a `peak` eased over `rise`, as one closed run of cubics cut square at both
ends. It is sampled at `STRETCH + 1` points, so its commands are the same at every moment. -/
def patchCubics (t : Tube) (s : Int) (len w0 w1 : Nat) (peak : Int) (rise : Nat) : List Cubic :=
  let L := t.length
  let pts := (List.range (STRETCH + 1)).map fun i =>
    let u := i * len / STRETCH
    let p := (s + u).toNat.min L
    let (c, h) := t.at p
    let half := (stretchWidth w0 w1 peak rise len u).toNat / 2
    let n := normal h
    (along c (-(half : Int)) n, along c half n, h)
  let lefts := pts.map (·.1)
  let rights := pts.map (·.2.1)
  let step : Int := len / STRETCH * 2
  let h0 := (pts.headD ((0, 0), (0, 0), 0)).2.2
  let h1 := (pts.getLastD ((0, 0), (0, 0), 0)).2.2
  let m0 := ((dir h0).1 * step / ONE, (dir h0).2 * step / ONE)
  let m1 := ((dir h1).1 * step / ONE, (dir h1).2 * step / ONE)
  match lefts.head?, lefts.getLast?, rights.head?, rights.getLast? with
  | some l0, some l1, some r0, some r1 =>
    throughC lefts m0 m1 ++ [lineC l1 r1] ++
      ((throughC rights m0 m1).map Cubic.rev).reverse ++ [lineC r0 l0]
  | _, _, _, _ => []

/-! ## A rounded crotch -/

/-- The radius of a crotch's fillet, in thousandths of a pixel: about four fifths of a pipe's
body, so a branch docks as a tree's does, widening into what it leaves. Where the branch leaves
less room, the fillet is the widest that fits (`crotch`). -/
def FILLET : Nat := 18000

/-- The distance between two points, in thousandths of a pixel. -/
def dist (a b : Int × Int) : Nat := Grow.isqrt ((a.1 - b.1).natAbs ^ 2 + (a.2 - b.2).natAbs ^ 2)

/-- The side a tube turns to first: `1` toward its normal, `-1` away, `0` for a straight tube. -/
def Tube.side (t : Tube) : Int :=
  match t.pieces.find? (·.turn != 0) with
  | some p => if p.turn < 0 then -1 else 1
  | none => 0

/-- **A circular arc as one cubic**, round the centre `c` from `p` to `q` (the shorter way), by
Riškus's handle `k = 4/3 · (√(2 q₁ q₂) − q₂) / (a × b)`. -/
def arcC (c p q : Int × Int) : Cubic :=
  let a := (p.1 - c.1, p.2 - c.2)
  let b := (q.1 - c.1, q.2 - c.2)
  let q1 := a.1 * a.1 + a.2 * a.2
  let q2 := q1 + a.1 * b.1 + a.2 * b.2
  let cross := a.1 * b.2 - a.2 * b.1
  if cross == 0 then lineC p q else
  let root : Int := Grow.isqrt (2 * q1 * q2).toNat
  let num := 4 * (root - q2)
  ⟨p, (c.1 + a.1 - num * a.2 / (3 * cross), c.2 + a.2 + num * a.1 / (3 * cross)),
   (c.1 + b.1 + num * b.2 / (3 * cross), c.2 + b.2 - num * b.1 / (3 * cross)), q⟩

/-- How far along a branch a crotch's fillet is looked for, in thousandths of a pixel. -/
def REACH : Nat := 160000

/-- **The rounded crotch** where `branch` leaves a straight body `parent` thousandths wide: the
branch starts on the body's centreline on its tangent and turns away. The fillet's centre stands
`R` off the body's edge and `R` off the branch's edge; the web is the region between the body's
edge, the branch's start and the fillet, filled in the bodies' tone. None where the branch does
not leave room for the fillet. -/
def crotchAt (parent : Nat) (branch : Tube) (bw : Nat) (R : Nat) : Option (List Cubic) :=
  let σ := branch.side
  if σ == 0 then none else
  let J := (branch.x, branch.y)
  let d := dir branch.head
  let n := normal branch.head
  let side := (σ * n.1, σ * n.2)
  let reach := min branch.length REACH
  let samples := (List.range (reach / 1000 + 1)).map fun i => (branch.at (i * 1000)).1
  let off : Int := (parent / 2 + R : Nat)
  let need : Int := (bw / 2 + R : Nat)
  let c (u : Int) := along (along J u d) off side
  let gap (u : Int) : Int := (samples.foldl (fun m p => min m (dist (c u) p)) 1000000000 : Nat) - need
  -- the first place past the branch's start where the fillet's circle clears the branch
  let found := (List.range (reach / 1000)).foldl (fun (acc : Bool × Option Int) i =>
    match acc with
    | (_, some u) => (true, some u)
    | (neg, none) =>
      let u : Int := ((i + 1) * 1000 : Nat)
      let g := gap u
      if g < 0 then (true, none) else if neg then (true, some u) else (false, none)) (false, none)
  match found.2 with
  | none => none
  | some hi =>
    -- halve the step ten times between the last place too close and the first clear
    let u := ((List.range 10).foldl (fun (lh : Int × Int) _ =>
      let mid := (lh.1 + lh.2) / 2
      if gap mid < 0 then (mid, lh.2) else (lh.1, mid)) (hi - 1000, hi)).2
    let cu := c u
    -- where the fillet touches the branch: the nearest sample, then a twentieth of a pixel at a
    -- time round it
    let i := (samples.zipIdx.foldl (fun (b : (Int × Int) × Nat) (p, k) =>
      if dist cu p < dist cu b.1 then (p, k) else b) (J, 0)).2
    let s2 := ((List.range 41).map fun j => i * 1000 + j * 50 - min (i * 1000) 1000).foldl
      (fun b s => if dist cu (branch.at s).1 < dist cu (branch.at b).1 then s else b) 0
    -- the branch's inner edge, from its start to the fillet, through `STRETCH + 1` points, a
    -- pixel inside the branch, so the web overlaps it and no seam shows where two fills meet
    let edge (inset : Nat) (s : Nat) : Int × Int :=
      let (p, h) := branch.at s
      along p (-(bw / 2 - inset : Nat) : Int) (σ * (normal h).1, σ * (normal h).2)
    let pts := (List.range (STRETCH + 1)).map fun k => edge 1000 (k * s2 / STRETCH)
    let T2 := edge 0 s2
    let T1 := along (along J u d) (parent / 2 : Nat) side
    let step : Int := (s2 / STRETCH * 2 : Nat)
    let h0 := branch.head
    let h1 := (branch.at s2).2
    some ([lineC T1 J, lineC J (pts.headD J)] ++
      throughC pts (along (0, 0) step (dir h0)) (along (0, 0) step (dir h1)) ++
      [lineC (pts.getLastD J) T2, arcC cu T2 T1])

/-- The cubics of a crotch's web, and a web of none at a point, with as many: a film grows one
from the other. -/
def WEB : Nat := STRETCH + 4
def noWeb (o : Int × Int) : List Cubic := List.replicate WEB (lineC o o)

/-- **The rounded crotch** at the widest fillet that fits: `FILLET`, or less by whole pixels two
at a time where the branch leaves less room. -/
def crotch (parent : Nat) (branch : Tube) (bw : Nat) : Option (List Cubic) :=
  ((List.range (FILLET / 2000)).map fun i => FILLET - 2000 * i).findSome? (crotchAt parent branch bw)

/-! ## A parting -/

/-- **A parting**: the ground between two round ends of a body `w` wide that face each other
across `len`, the middle of it `s + len/2` along the tube. Each end is a half circle of the
body's half width, eased down to nothing as the parting closes to under `GAP`, so a valve that
opens fuses its two ends into one body. It reaches a pixel past each edge, so no hairline stays. A
parting of no length is nothing. Ten cubics, at every moment. -/
def partCubics (t : Tube) (s : Int) (len w gap : Nat) : List Cubic :=
  let (c, h) := t.at (s + (len / 2 : Nat)).toNat
  let d := dir h
  let n := normal h
  let r : Int := (w / 2 * min len gap / max 1 gap : Nat)
  let H : Int := (w / 2 + 1000 : Nat)
  let k := r * KAPPA / 1000000
  let half : Int := (len / 2 : Nat)
  let a := along c (-(half + r)) d
  let b := along c (half + r) d
  let tl := along a (-H) n
  let tr := along b (-H) n
  let bl := along a H n
  let br := along b H n
  let bt := along b (-r) n
  let bm := along b (-r) d
  let bb := along b r n
  let at_ := along a (-r) n
  let am := along a r d
  let ab := along a r n
  [lineC tl tr, lineC tr bt,
   ⟨bt, along bt (-k) d, along bm (-k) n, bm⟩, ⟨bm, along bm k n, along bb (-k) d, bb⟩,
   lineC bb br, lineC br bl, lineC bl ab,
   ⟨ab, along ab k d, along am k n, am⟩, ⟨am, along am (-k) n, along at_ k d, at_⟩,
   lineC at_ tl]

-- a parallel of a quarter turn of radius 20 px, 5 px inside, is a quarter turn of radius 15 px
#guard (Tube.offset ⟨0, 0, 0, 8000, [⟨31416, 1570796⟩]⟩ 5000).pieces == [⟨23563, 1570796⟩]
-- a parallel of a straight tube starts beside it
#guard (Tube.offset (straight 0 0 0 8000 50000) 11000).y == 11000
-- the smoothstep runs from nothing to one, and is a half at the half
#guard smooth 0 == 0 && smooth 500 == 500 && smooth 1000 == 1000
-- a body of one width is its two parallels and two round caps of two cubics each
#guard (bodyCubics (straight 0 0 0 12000 100000) 22000 true true).length == 2 + 2 + 2 + 2
-- a stretch is sampled at the same points whatever its width
#guard (patchCubics (straight 0 0 0 12000 100000) 20000 30000 22000 22000 4000 15000).length ==
  2 * STRETCH + 2
-- a parting is ten cubics, open or closed
#guard (partCubics (straight 0 0 0 12000 100000) 40000 4000 22000 4000).length == 10
#guard (partCubics (straight 0 0 0 12000 100000) 40000 0 22000 4000).length == 10
-- a branch that leaves a pipe of 22 px on its tangent and turns 45° away gets a fillet
#guard (crotch 22000 ⟨0, 0, 0, 12000, [⟨26000 * 785398 / 1000000, -785398⟩, ⟨34000, 0⟩,
  ⟨26000 * 785398 / 1000000, 785398⟩, ⟨100000, 0⟩]⟩ 22000).isSome

end Tools.View.Tube
