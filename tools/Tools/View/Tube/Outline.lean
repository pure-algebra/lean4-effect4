import Tools.View.Tube.Form
import Tools.View.Organic

/-!
# Tools.View.Tube.Outline — solid bodies: a tube's outline, a parting

The owner's ruling of 2026-10-13 (decisions row 370): a tube is a **solid body**, filled in one
tone, and its outline is smooth everywhere, with no kink.

* **A body's outline** (`bodyCubics`): the tube's two parallels at half its width, joined by its
  caps, round where the tube is closed and cut square where it opens to the world. The parallel of
  an arc is an arc of the same turn and of a radius less or more by the distance (`Tube.offset`),
  so the outline of a body of one width is exact, and as smooth as its centreline: the bend law
  makes every piece meet the next on its tangent.
* **A stretch of changing width** and **a join** are the kit's (`Tools.View.Tube.Kit`, the kit's
  slice S24): a stretch's sides are its trapezoid profile carried onto the tube, and every notch
  where two bodies meet is blended in closed form.

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

/-- The distance between two points, in thousandths of a pixel. -/
def dist (a b : Int × Int) : Nat := Grow.isqrt ((a.1 - b.1).natAbs ^ 2 + (a.2 - b.2).natAbs ^ 2)

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

/-- **The rings of a parting**: the line of `line` round each round end that faces the gap, as
two closed half rings. An end of less than three lines' radius has none. -/
def ringCubics (t : Tube) (s : Int) (len w gap line : Nat) : List (List Cubic) :=
  let (c, h) := t.at (s + (len / 2 : Nat)).toNat
  let d := dir h
  let n := normal h
  let r : Int := (w / 2 * min len gap / max 1 gap : Nat)
  -- an end narrower than three lines has no ring yet: it is still fusing, or just parting
  let ri : Int := if r < 3 * (line : Int) then r else r - line
  let k := r * KAPPA / 1000000
  let ki := ri * KAPPA / 1000000
  let half : Int := (len / 2 : Nat)
  let a := along c (-(half + r)) d
  let b := along c (half + r) d
  let half_ (o : Int × Int) (rr kk : Int) (sg : Int) : Cubic × Cubic :=
    -- from the top of the circle round its side toward the gap to its bottom
    let top := along o (-rr) n
    let mid := along o (sg * rr) d
    let bot := along o rr n
    (⟨top, along top (sg * kk) d, along mid (-kk) n, mid⟩, ⟨mid, along mid kk n, along bot (sg * kk) d, bot⟩)
  let (b1, b2) := half_ b r k (-1)
  let (bi1, bi2) := half_ b ri ki (-1)
  let (a1, a2) := half_ a r k 1
  let (ai1, ai2) := half_ a ri ki 1
  [[b1, b2, lineC b2.p3 bi2.p3, Cubic.rev bi2, Cubic.rev bi1, lineC bi1.p0 b1.p0],
   [a1, a2, lineC a2.p3 ai2.p3, Cubic.rev ai2, Cubic.rev ai1, lineC ai1.p0 a1.p0]]

-- a parallel of a quarter turn of radius 20 px, 5 px inside, is a quarter turn of radius 15 px
#guard (Tube.offset ⟨0, 0, 0, 8000, [⟨31416, 1570796⟩]⟩ 5000).pieces == [⟨23563, 1570796⟩]
-- a parallel of a straight tube starts beside it
#guard (Tube.offset (straight 0 0 0 8000 50000) 11000).y == 11000
-- a body of one width is its two parallels and two round caps of two cubics each
#guard (bodyCubics (straight 0 0 0 12000 100000) 22000 true true).length == 2 + 2 + 2 + 2
-- a parting is ten cubics, open or closed
#guard (partCubics (straight 0 0 0 12000 100000) 40000 4000 22000 4000).length == 10
#guard (partCubics (straight 0 0 0 12000 100000) 40000 0 22000 4000).length == 10

end Tools.View.Tube
