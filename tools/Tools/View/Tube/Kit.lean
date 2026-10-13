import Tools.View.Tube.Form
import Tools.View.Picture
import Whatwg.Svg.Geometry.Tube.Bulge

/-!
# Tools.View.Tube.Kit — the pen's joins and stretches drawn by the kit

Slice M7 of the motion plan (`docs/research/2026-10-13-motion-everywhere/README.md`), its first two
steps. The kit's slice S24 blends every notch where two bodies meet in closed form, by G2 corners
exact in rationals where the walls allow and by a rolling ball otherwise
(`Whatwg/Svg/Geometry/Tube/Blend.lean`, decisions row 371). The pen keeps its own tubes, in
thousandths of a pixel and millionths of a radian, and hands a join's tubes to the kit here: a
tube is mapped to the kit's (`toKit`, the pen's π to the kit's), the kit's notches are blended,
and each web comes back as the pen's cubics (`fromKit`).

**A stretch** (`bulge`), where a body's width changes along it (a reducer, a sleeve, a swell), takes
the kit's trapezoid profile (`Whatwg/Svg/Geometry/Tube/Bulge.lean`, `Tube.Profile`), whose second
derivative is continuous, so a side meets its pipe with no jump of curvature: the owner's "straight
edge on the bulge" was the smoothstep's (the tube language's `algorithms.md`, B1 to B3). Each side
is the profile's cubics carried onto the tube by the pen's frames and their first derivative: the
kit's own sides where the tube is straight (G2), and sides that keep their tangent on a bend (G1).

**One shape at every moment.** A film writes a join's webs, and a stretch's outline, at each of its
moments as one SMIL path, so the path's commands must agree in number and kind at every moment. A
join has a fixed count of slots (one for each of its notches, a fallback taking its notch's slot),
and every web is padded to `PAD` cubics with pieces of no length at its last point; a slot with no
web is a web of no size at the junction. A stretch is 28 cubics, whatever its sizes and its ends.
-/

namespace Tools.View.Tube.Kit
open Tools.View
open Whatwg.Svg.Value (Vec)
abbrev KTube := Whatwg.Svg.Value.Tube
abbrev KCubic := Whatwg.Svg.Value.Cubic
abbrev Notch := Whatwg.Svg.Value.Tube.Notch

/-- The pen's π, in millionths of a radian. -/
def PEN_PI : Rat := 3141593

/-- An angle of the pen, millionths of a radian, as the kit's: the pen's π is the kit's. -/
def angle (a : Int) : Rat := (a : Rat) * Whatwg.Svg.Value.Angle.pi / PEN_PI

/-- **A tube as the kit's**, `width` thousandths of a pixel wide (a body's width). -/
def toKit (t : Tube) (width : Nat) : KTube :=
  { start := ⟨(t.x : Rat) / 1000, (t.y : Rat) / 1000⟩
    heading := angle t.head
    width := (width : Rat) / 1000
    pieces := t.pieces.map fun p => ⟨(p.len : Rat) / 1000, angle p.turn⟩ }

/-- A coordinate of the kit, in pixels, as thousandths of a pixel, rounded. -/
def milli (r : Rat) : Int := (r * 1000 + 1 / 2).floor

/-- A point of the kit as the pen's. -/
def pt (v : Vec) : Int × Int := (milli v.x, milli v.y)

/-- **A cubic of the kit as the pen's.** -/
def fromKit (c : KCubic) : Cubic := ⟨pt c.p0, pt c.p1, pt c.p2, pt c.p3⟩

/-- The cubics each web is padded to. -/
def PAD : Nat := 12

/-- A web of no size at a point. -/
def none_ (o : Int × Int) : List Cubic := List.replicate PAD ⟨o, o, o, o⟩

/-- A web padded to `PAD` cubics by pieces of no length at its last point. -/
def pad (o : Int × Int) (cs : List Cubic) : List Cubic :=
  match cs.getLast? with
  | none => none_ o
  | some c => cs ++ List.replicate (PAD - cs.length) ⟨c.p3, c.p3, c.p3, c.p3⟩

/-- **The webs of a join's notches, one for each slot**: a notch with no fallback is a slot; its
web, or where it has none, the first of its fallbacks' that has one, or a web of no size at the
junction. The band and the radius are the widths' rule's, inset by `grow` pixels. -/
def slots (ns : List Notch) (grow : Rat) : List (List Cubic) :=
  let webOf (n : Notch) : Option (List KCubic) := (n.webCurve n.band n.radius grow).map (·.1)
  let ws := ns.map webOf
  (ns.zip ws).zipIdx.filterMap fun ((n, w), i) =>
    match n.fallbackOf with
    | some _ => none
    | none =>
      let o := pt n.junction
      let fb := (ns.zip ws).findSome? fun (n', w') => if n'.fallbackOf == some i then w' else none
      some (match w.orElse fun _ => fb with
        | some cs => pad o (cs.map fromKit)
        | none => none_ o)

/-- The length along a straight tube from its start to the foot of a point on its centreline. -/
def alongTo (t : KTube) (p : Vec) : Rat :=
  let d := Whatwg.Svg.Value.Angle.dir t.heading 12
  (p.x - t.start.x) * d.x + (p.y - t.start.y) * d.y

/-- **A crotch's webs**: a branch that leaves a body on its tangent and turns away, `grow`
thousandths of a pixel inset. Two slots, the branch's two walls against the body's. -/
def crotch (body branch : Tube) (bw brw : Nat) (grow : Nat) : List (List Cubic) :=
  slots (Whatwg.Svg.Value.Tube.Join.crotch (toKit body bw) (toKit branch brw)) ((grow : Rat) / 1000)

/-- **A fork's webs**: two arms that leave one point of a parent, the parent cut where they leave
so that it arrives there, as the kit's fork asks. Three slots: between the arms, and each arm's
outer wall against the parent's. -/
def fork (parent b c : Tube) (pw bw cw : Nat) (grow : Nat) : List (List Cubic) :=
  let kp := toKit parent pw
  let kb := toKit b bw
  let trunk : KTube := kp.cut 0 (max 0 (alongTo kp kb.start))
  slots (Whatwg.Svg.Value.Tube.Join.fork trunk kb (toKit c cw)) ((grow : Rat) / 1000)

/-! ## A stretch: the kit's profile on the tube -/

/-- The curvature of a tube's centreline `s` thousandths along it, per pixel: of the piece just
after `s` (`ahead`), or just before it. -/
def kappa : List Piece → Nat → Bool → Rat
  | [], _, _ => 0
  | q :: rest, s, ahead =>
    if (if ahead then s < q.len else s ≤ q.len) then
      (if q.len = 0 then 0 else (q.turn : Rat) / ((q.len : Rat) * 1000))
    else kappa rest (s - q.len) ahead

/-- **A frame of the pen's tube**, `s` thousandths along it, in the kit's numbers: the point on
the centreline, the unit tangent, and the curvature just after and just before. The stretch takes
the pen's frames, so its sides meet the body's outline on the same numbers. -/
structure Frame where
  at_ : Vec
  d : Vec
  ahead : Rat
  behind : Rat

/-- The frame `s` thousandths along a tube. -/
def frameOf (t : Tube) (s : Nat) : Frame :=
  let ((x, y), h) := t.at s
  let (dx, dy) := dir h
  { at_ := ⟨(x : Rat) / 1000, (y : Rat) / 1000⟩, d := ⟨(dx : Rat) / ONE, (dy : Rat) / ONE⟩
    ahead := kappa t.pieces s true, behind := kappa t.pieces s false }

/-- The cubics each side of a stretch runs along its middle. -/
def MIDDLE : Nat := 2

/-- **One side of a stretch**, in its own plane: `u` along the stretch and `h` the half width. The
kit's trapezoid profile rises from `a` to `m` over `r`, the middle holds `m` in `MIDDLE` lines,
and the profile falls to `b` over `r` (`Whatwg/Svg/Geometry/Tube/Bulge.lean`, `Tube.side`). -/
def sideOf (len r a m b : Rat) : List KCubic :=
  let cs := Whatwg.Svg.Value.Tube.Profile.trapezoid.cubics.getD []
  let ramp (u₀ h₀ h₁ : Rat) : List KCubic :=
    cs.map (Whatwg.Svg.Value.Cubic.map fun q => ⟨u₀ + q.x * r, h₀ + q.y * (h₁ - h₀)⟩)
  let at_ (i : Nat) : Vec := ⟨r + (len - 2 * r) * i / MIDDLE, m⟩
  ramp 0 a m ++ (List.range MIDDLE).map (fun i => Whatwg.Svg.Value.Cubic.line (at_ i) (at_ (i + 1))) ++
    ramp (len - r) m b

/-- **A side carried onto the tube**: each end of a cubic to the point `h` off the centreline on
the side `σ`, and each handle by the map's first derivative there, `(1 − κσh)` along the tangent
and `σ` along the normal. Where the tube is straight the map is affine, so the side is the kit's
profile exactly. Each joint's two handles take one tangent, so the side keeps its tangent on a
bend (G1). `inside` says which joints lie on the tube; a joint past an end stands at that end on
its edge, `edge0` or `edge1` off, with no handle. -/
def carry (frames : List Frame) (inside : List (Option Bool)) (σ edge0 edge1 : Rat)
    (side : List KCubic) : List KCubic :=
  let place (h : Rat) (f : Frame) (o : Option Bool) : Vec :=
    f.at_ + Vec.scale (σ * (match o with | some false => edge0 | some true => edge1 | none => h)) f.d.perp
  let handle (p q : Vec) (f : Frame) (o : Option Bool) (ahead : Bool) : Vec :=
    match o with
    | some _ => place p.y f o
    | none =>
      let k := if ahead then f.ahead else f.behind
      place p.y f o + Vec.scale ((1 - k * σ * p.y) * (q.x - p.x)) f.d + Vec.scale (σ * (q.y - p.y)) f.d.perp
  side.zipIdx.filterMap fun (c, i) =>
    match frames[i]?, frames[i + 1]?, inside[i]?, inside[i + 1]? with
    | some f0, some f1, some o0, some o1 =>
      some ⟨place c.p0.y f0 o0, handle c.p0 c.p1 f0 o0 true, handle c.p3 c.p2 f1 o1 false, place c.p3.y f1 o1⟩
    | _, _, _, _ => none

/-- The handle of a quarter circle of radius one, `4(√2 − 1)/3`. -/
def KAPPA : Rat := 5522847 / 10000000

/-- **An end of a stretch**, from `a` to `b` round the point `c` with the tangent `d` pointing out
of the stretch, its normal `n` from `a` toward `b`: a half circle of radius `r` where the end is
round, else the straight cut in two halves. Two cubics either way. -/
def endOf (a b c d n : Vec) (r : Rat) (round : Bool) : List KCubic :=
  if round then
    let tip := c + Vec.scale r d
    let k := KAPPA * r
    [⟨a, a + Vec.scale k d, tip - Vec.scale k n, tip⟩, ⟨tip, tip + Vec.scale k n, b + Vec.scale k d, b⟩]
  else
    let m := Vec.scale (1 / 2) (a + b)
    [Whatwg.Svg.Value.Cubic.line a m, Whatwg.Svg.Value.Cubic.line m b]

/-- **A stretch's outline**: the part of the tube from `s` along it, `len` long, its width eased by
the kit's trapezoid profile from `w0` to `top` and from `top` to `w1` over `rise` at its ends (at
most half the stretch), all in thousandths of a pixel. Its left side, its end, its right side
back, its start: one closed ring of 28 cubics, in the kit's numbers, whatever its sizes and its
ends. -/
def bulgeK (t : Tube) (s : Int) (len w0 w1 top rise : Nat) (roundStart roundEnd : Bool := false) :
    List KCubic :=
  let k (n : Nat) : Rat := (n : Rat) / 1000
  let r := min (k rise) (k len / 2)
  let side := sideOf (k len) r (k w0 / 2) (k top / 2) (k w1 / 2)
  let us := side.map (·.p0.x) ++ [(side.getLast?.map (·.p3.x)).getD 0]
  let L := t.length
  -- each joint's place along the tube, in thousandths, and whether it lies past an end
  let ats := us.map fun u => (s : Rat) + u * 1000
  let inside := ats.map fun a => if a < 0 then some false else if (L : Rat) < a then some true else none
  let frames := ats.map fun a => frameOf t ((max 0 (min (L : Int) (a + 1 / 2).floor)).toNat)
  let left := carry frames inside (-1) (k w0 / 2) (k w1 / 2) side
  let right := carry frames inside 1 (k w0 / 2) (k w1 / 2) side
  match left.head?, left.getLast?, right.head?, right.getLast?, frames.head?, frames.getLast? with
  | some l0, some l1, some r0, some r1, some f0, some f1 =>
    left ++ endOf l1.p3 r1.p3 f1.at_ f1.d f1.d.perp (k w1 / 2) roundEnd ++
      Whatwg.Svg.Value.Cubic.reverseAll right ++
      endOf r0.p0 l0.p0 f0.at_ (Vec.scale (-1) f0.d) (Vec.scale (-1) f0.d.perp) (k w0 / 2) roundStart
  | _, _, _, _, _, _ => []

/-- **A stretch's outline**, the pen's: `bulgeK` in thousandths of a pixel. A stretch is 28 cubics
at every moment of a film, so a film writes it as one path whose commands agree. -/
def bulge (t : Tube) (s : Int) (len w0 w1 top rise : Nat) (roundStart roundEnd : Bool := false) :
    List Cubic :=
  (bulgeK t s len w0 w1 top rise roundStart roundEnd).map fromKit

-- a stretch is 28 cubics, whatever its sizes, its tube and its ends, and a closed ring
#guard (bulge ⟨0, 0, 0, 12000, [⟨100000, 0⟩]⟩ 20000 30000 22000 22000 26000 15000).length == 28
#guard (bulge ⟨0, 0, 0, 12000, [⟨40000, 0⟩, ⟨31416, 1570796⟩]⟩ 30000 40000 22000 22000 30000 5000 true true).length == 28
#guard (bulge ⟨0, 0, 0, 12000, [⟨100000, 0⟩]⟩ 0 0 0 0 0 1).length == 28
#guard [false, true].all fun round =>
  let cs := bulgeK ⟨0, 0, 0, 12000, [⟨40000, 0⟩, ⟨31416, 1570796⟩]⟩ 30000 40000 22000 22000 30000 5000 round round
  (cs.head?.map (·.p0)) == (cs.getLast?.map (·.p3))
-- on a straight run the side is the kit's own: its ramp is the kit's `rampCubics`, exactly
#guard (bulgeK ⟨0, 0, 0, 12000, [⟨100000, 0⟩]⟩ 20000 30000 22000 22000 26000 10000).take 5 ==
  Whatwg.Svg.Value.Tube.rampCubics ⟨20, 0⟩ ⟨1, 0⟩ (-1) 0 10 11 13
    (Whatwg.Svg.Value.Tube.Profile.trapezoid.cubics.getD [])

end Tools.View.Tube.Kit
