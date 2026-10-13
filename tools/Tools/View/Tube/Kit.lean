import Tools.View.Tube.Form
import Tools.View.Picture
import Whatwg.Svg.Geometry.Tube.Blend

/-!
# Tools.View.Tube.Kit — the pen's joins drawn by the kit's blend

Slice M7 of the motion plan (`docs/research/2026-10-13-motion-everywhere/README.md`), its first
step. The kit's slice S24 blends every notch where two bodies meet in closed form, by G2 corners
exact in rationals where the walls allow and by a rolling ball otherwise
(`Whatwg/Svg/Geometry/Tube/Blend.lean`, decisions row 371). The pen keeps its own tubes, in
thousandths of a pixel and millionths of a radian, and hands a join's tubes to the kit here: a
tube is mapped to the kit's (`toKit`, the pen's π to the kit's), the kit's notches are blended,
and each web comes back as the pen's cubics (`fromKit`).

**One shape at every moment.** A film writes a join's webs at each of its moments as one SMIL
path, so the path's commands must agree in number and kind at every moment. A join has a fixed
count of slots (one for each of its notches, a fallback taking its notch's slot), and every web
is padded to `PAD` cubics with pieces of no length at its last point; a slot with no web is a web
of no size at the junction.
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

end Tools.View.Tube.Kit
