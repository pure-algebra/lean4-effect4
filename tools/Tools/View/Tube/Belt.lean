import Tools.View.Picture
import Tools.View.Tube.Trig

/-!
# Tools.View.Tube.Belt — a string pulled taut round pegs

The pegs note (`docs/research/2026-10-13-tube-language/pegs.md`, decisions row 374) draws every
body as a string round pegs. A **peg** is a centre and a signed radius. The body wraps a convex
peg (`r > 0`); the string bends back round a concave one (`r < 0`): a notch, a crotch, a neck.
The string runs clockwise on screen (y down), the body on its right.

* **The tangent.** Between two pegs the string runs on their common tangent. Its outward normal
  `n` solves `n · (cⱼ − cᵢ) = ρᵢ − ρⱼ` with `|n| = 1`: for `D = cⱼ − cᵢ`, `e = ρᵢ − ρⱼ` and
  `s = √(|D|² − e²)`, `n = (e·Dx + s·Dy, e·Dy − s·Dx) / |D|²`. One square root (`normal`).
* **The arc.** Round a peg the string follows its circle from the normal it arrives on to the one
  it leaves on, turning clockwise round a convex peg and back round a concave one. The turn is
  halved twice by bisecting unit vectors, so no angle is computed. Each quarter of turn `φ` is one
  cubic whose handles are `4/3 · tan(φ/4)` of the radius (`Peg.arc`).
* **The belt.** Four cubics round each peg and one along each tangent, so a body's path has five
  cubics a peg, however its pegs move (`belt`).

Units: points and radii in thousandths of a pixel, the pen's; a unit vector at the scale `ONE`.

The laws of the note's §8: the belt chains and closes (`chained`); every joint keeps its tangent
(`smooth`); the casing, the belt round the same pegs each one line smaller, has the outline's
normals exactly (`normal_inset`), so it is the outline moved in by the line, to the rounding of
one division (`insetBy`); a belt of moved pegs has the same normals (`normal_move`).
-/

namespace Tools.View.Tube

/-- **A peg**: a centre, and a radius signed by its side. Above zero the body wraps it; below zero
the string bends back round it. In thousandths of a pixel. -/
structure Peg where
  c : Int × Int
  r : Int
deriving Repr, DecidableEq, Inhabited

namespace Belt

/-- The square root of a whole number, rounded down; zero below zero. -/
def isqrt (n : Int) : Int := (Nat.sqrt n.toNat : Int)

def dot (u v : Int × Int) : Int := u.1 * v.1 + u.2 * v.2

def cross (u v : Int × Int) : Int := u.1 * v.2 - u.2 * v.1

/-- The unit vector along `v`, at the scale `ONE`. -/
def unit (v : Int × Int) : Int × Int :=
  let l := isqrt (dot v v)
  if l = 0 then (ONE, 0) else (v.1 * ONE / l, v.2 * ONE / l)

/-- **The common tangent's outward normal** from peg `p` to peg `q`, at the scale `ONE`; nothing
where the pegs share no tangent on this side (one holds the other). Two pegs that touch give
`e · D / |D|²`, the touching point's normal; so do two that overlap by a thousandth of a pixel at
most, the rounding of a peg placed to touch. -/
def normal (p q : Peg) : Option (Int × Int) :=
  let dx := q.c.1 - p.c.1
  let dy := q.c.2 - p.c.2
  let l2 := dx * dx + dy * dy
  let e := p.r - q.r
  if l2 = 0 ∨ l2 + 2 * (e.natAbs : Int) < e * e then none
  else
    let s := isqrt ((l2 - e * e) * ONE * ONE)
    some ((e * dx * ONE + s * dy) / l2, (e * dy * ONE - s * dx) / l2)

/-- The unit vector half way round from `u` to `v`, turning clockwise on screen (`σ = 1`) or back
(`σ = −1`), the whole turn taken in `[0, 2π)`. From a quarter turn to three quarters the chord's
normal `σ · (u − v)⊥` gives it; nearer no turn the sum `u + v`, and nearer a whole turn the sum's
opposite. Each is at least `√2` long where it is used, so the unit is exact to the scale. -/
def half (σ : Int) (u v : Int × Int) : Int × Int :=
  if dot u v ≤ 0 then unit (σ * (v.2 - u.2), σ * (u.1 - v.1))
  else if 0 ≤ σ * cross u v then unit (u.1 + v.1, u.2 + v.2)
  else unit (-(u.1 + v.1), -(u.2 + v.2))

/-- The straight segment from `a` to `b`, its controls at a third and two thirds. -/
def line (a b : Int × Int) : Cubic :=
  ⟨a, (a.1 + (b.1 - a.1) / 3, a.2 + (b.2 - a.2) / 3),
    (a.1 + 2 * (b.1 - a.1) / 3, a.2 + 2 * (b.2 - a.2) / 3), b⟩

end Belt

open Belt

/-- The point of a peg's string at the unit normal `u`: the centre and the signed radius along
`u`, so a concave peg's point stands on the side away from `u`. -/
def Peg.at (p : Peg) (u : Int × Int) : Int × Int :=
  (p.c.1 + p.r * u.1 / ONE, p.c.2 + p.r * u.2 / ONE)

/-- One cubic of a peg's arc, from the unit normal `a` to `b`, with handles `h` long along the
string's travel, `u⊥ = (−u_y, u_x)` at either end, round either kind of peg. -/
def Peg.piece (p : Peg) (h : Int) (a b : Int × Int) : Cubic :=
  let a₀ := p.at a
  let b₀ := p.at b
  ⟨a₀, (a₀.1 - h * a.2 / ONE, a₀.2 + h * a.1 / ONE),
    (b₀.1 + h * b.2 / ONE, b₀.2 - h * b.1 / ONE), b₀⟩

/-- **The arc round a peg** from the normal `u` it arrives on to the normal `v` it leaves on, as
four cubics. The turn is halved, `m`, and halved again, `q₁` and `q₃`; the eighth `w` gives
`tan(φ/4) = σ · (u × w) / (1 + u · w)` for a quarter's turn `φ`, and the handles are `4/3` of it
times the radius. -/
def Peg.arc (p : Peg) (u v : Int × Int) : List Cubic :=
  let σ : Int := if 0 ≤ p.r then 1 else -1
  let m := half σ u v
  let q₁ := half σ u m
  let q₃ := half σ m v
  let w := half σ u q₁
  let t := σ * cross u w * ONE / (ONE * ONE + dot u w)
  let h := 4 * t * (p.r.natAbs : Int) / (3 * ONE)
  [p.piece h u q₁, p.piece h q₁ m, p.piece h m q₃, p.piece h q₃ v]

/-- **The belt** round pegs in order: for each peg, its arc from the normal it arrives on to the
one it leaves on, then the line along the tangent to the next peg. Nothing where two neighbours
share no tangent. -/
def Belt.normals (ps : List Peg) : Option (List (Int × Int)) :=
  (ps.zip (ps.rotateLeft 1)).mapM fun pq => normal pq.1 pq.2

/-- Build a belt with normals already computed for its cyclic neighbour pairs. -/
def Belt.withNormals (ps : List Peg) (ns : List (Int × Int)) : List Cubic :=
  (ps.zip ((ps.rotateLeft 1).zip ((ns.rotateRight 1).zip ns))).flatMap fun (p, q, u, v) =>
    p.arc u v ++ [line (p.at v) (q.at v)]

def belt (ps : List Peg) : Option (List Cubic) := do
  let ns ← Belt.normals ps
  pure (Belt.withNormals ps ns)

/-! ## The laws -/

/-- A peg one line `w` smaller: the casing's peg, a line inside the body round either kind. -/
def Peg.inset (w : Int) (p : Peg) : Peg := ⟨p.c, p.r - w⟩

/-- A peg moved by `d`. -/
def Peg.move (d : Int × Int) (p : Peg) : Peg := ⟨(p.c.1 + d.1, p.c.2 + d.2), p.r⟩

/-- Outline and casing share one tangent calculation per neighbour pair. -/
def Belt.outlines (w : Int) (ps : List Peg) : Option (List Cubic × List Cubic) := do
  let ns ← Belt.normals ps
  pure (Belt.withNormals ps ns, Belt.withNormals (ps.map (Peg.inset w)) ns)

/-- **The casing's normals are the outline's** (law 3): a tangent depends on the difference of
the radii, which an inset keeps. -/
theorem normal_inset (w : Int) (p q : Peg) : normal (p.inset w) (q.inset w) = normal p q := by
  have h : p.r - w - (q.r - w) = p.r - q.r := by omega
  simp only [normal, Peg.inset, h]

/-- **A moved pair's normal is the pair's** (law 4's first step): a tangent depends on the
difference of the centres, which a move keeps. -/
theorem normal_move (d : Int × Int) (p q : Peg) : normal (p.move d) (q.move d) = normal p q := by
  have h₁ : q.c.1 + d.1 - (p.c.1 + d.1) = q.c.1 - p.c.1 := by omega
  have h₂ : q.c.2 + d.2 - (p.c.2 + d.2) = q.c.2 - p.c.2 := by omega
  simp only [normal, Peg.move, h₁, h₂]

/-- Each segment ends where the next starts, and the last where the first starts (law 1's
closure). -/
def chained (cs : List Cubic) : Bool :=
  (cs.zip (cs.rotateLeft 1)).all fun ab => ab.1.p3 == ab.2.p0

/-- A segment with every point at its start: a peg's arc of no turn. -/
def Cubic.still (c : Cubic) : Bool := c.p0 == c.p1 && c.p1 == c.p2 && c.p2 == c.p3

/-- The handles at a joint: the first's arriving one and the second's leaving one. Where a handle
is nothing the chord stands for it. -/
def handles (a b : Cubic) : (Int × Int) × (Int × Int) :=
  let d (p q : Int × Int) : Int × Int := (q.1 - p.1, q.2 - p.2)
  (if a.p2 == a.p3 then d a.p0 a.p3 else d a.p2 a.p3,
   if b.p0 == b.p1 then d b.p0 b.p3 else d b.p0 b.p1)

/-- **Every joint keeps its tangent** (law 2), to `tol` thousandths of a pixel: at each joint
the two handles point the same way, and the tip of the shorter stands within `tol` of the longer
one's line. Segments of no turn are passed over. -/
def smooth (tol : Int) (cs : List Cubic) : Bool :=
  let ds := cs.filter (!Cubic.still ·)
  (ds.zip (ds.rotateLeft 1)).all fun ab =>
    let (s, t) := handles ab.1 ab.2
    let x := cross s t
    0 ≤ dot s t && x * x ≤ tol * tol * max (dot s s) (dot t t)

/-- **The casing is the outline moved in by `w`** (law 3), to `tol` thousandths of a pixel: each
segment's start stands `w` from the outline's. -/
def insetBy (w tol : Int) (outline casing : List Cubic) : Bool :=
  outline.length == casing.length &&
    (outline.zip casing).all fun ab =>
      let dx := ab.1.p0.1 - ab.2.p0.1
      let dy := ab.1.p0.2 - ab.2.p0.2
      let l := isqrt (dx * dx + dy * dy)
      w - tol ≤ l && l ≤ w + tol

/-! ## Guards: a pipe, a taper, a bend, a belt round rings -/

/-- A pipe: two pegs of one size, a body of ten pixels' half width. -/
def pipe : List Peg := [⟨(24000, 24000), 10000⟩, ⟨(144000, 24000), 10000⟩]

/-- A taper: two pegs of two sizes. -/
def taper : List Peg := [⟨(24000, 24000), 14000⟩, ⟨(144000, 24000), 7000⟩]

/-- A bend of a quarter turn about `(60000, 48000)`, radius 24 px, half width 7: the outer wall
round a convex peg, the inner round a concave one. -/
def bend : List Peg :=
  [⟨(18000, 24000), 7000⟩, ⟨(60000, 48000), 31000⟩, ⟨(84000, 96000), 7000⟩,
   ⟨(60000, 48000), -17000⟩]

/-- Four rings and a string round them, as in the reference. -/
def rings : List Peg :=
  [⟨(36000, 36000), 15000⟩, ⟨(120000, 36000), 15000⟩, ⟨(120000, 96000), 11000⟩,
   ⟨(36000, 96000), 15000⟩]

#guard [pipe, taper, bend, rings].all fun ps =>
  match belt ps, belt (ps.map (Peg.inset 2000)) with
  | some o, some c => o.length == 5 * ps.length && chained o && chained c &&
      smooth 3 o && smooth 3 c && insetBy 2000 2 o c
  | _, _ => false

-- A belt of moved pegs is the belt moved.
#guard [pipe, taper, bend, rings].all fun ps =>
  belt (ps.map (Peg.move (12000, -24000))) == (belt ps).map (List.map (Cubic.move 12000 (-24000)))

-- Pegs one inside the other share no tangent: no belt. Pegs placed to touch, rounded a thousandth
-- of a pixel into each other, touch.
#guard belt [⟨(0, 0), 20000⟩, ⟨(5000, 0), 5000⟩] == none
#guard (normal ⟨(0, 0), 19000⟩ ⟨(18248, 14000), -4000⟩).isSome

end Tools.View.Tube
