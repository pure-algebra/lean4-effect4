import Tools.View.Tube.Form
import Tools.View.SvgOut
import Whatwg.Svg.Geometry.Spring

/-!
# Tools.View.Tube.Draw — one pen, one amount, and every transition a morph

**One pen.** Every mark is a tube's centreline stroked: the wall, the lumen inside it, a plug in
the lumen, a collar round it, a unit of its contents. A tube is drawn as strokes of one path, as a
cartographer draws a road with its casing: every wall first, then every lumen, then the plugs and
the contents (`Mark.layer`). Where two tubes meet, the later lumen covers the earlier walls, so a
junction is one open lumen and needs no shape of its own. The wall is `WALL` thick and the lumen
keeps `CLEAR` round the contents, whatever the tube. Every width is a whole, even number of pixels
and a picture is drawn at one pixel to the pixel, so a straight run's edges fall on pixel edges.

**One amount.** A unit of contents has one area, `AREA` square pixels, in every tube: in a tube
whose contents are `c` pixels wide its slot is `AREA / c` long. Every width of the ladder divides
the area (`ladder_divides`), so every slot is a whole number of pixels. A unit is drawn as a pill,
a liquid plug with a round meniscus at each end, as a plug of liquid stands in a capillary
(Bretherton, "The motion of long bubbles in tubes", 1961), a `MENISCUS` from the next; every width
of the ladder leaves room for a whole pill in its slot (`ladder_pills`). A unit that passes from a
narrow tube into a wide one shortens, as water does.

**Every transition a morph, timed.** A mark says how it comes into its pose with the kit's
`Transition` (`Mark.move`, `Mark.shape`), so a cause moves before its effect. How a picture
becomes the next is `Tools.View.Tube.Motion`.
-/

namespace Tools.View.Tube
open Tools.View Whatwg.Html
open Whatwg.Svg.Value (Decimal Pen Point Path)

/-! ## The pen and the amount -/

/-- The wall's thickness, on each side of a tube, in thousandths of a pixel: one for every tube. -/
def WALL : Nat := 3000
/-- The clearance between the contents and the wall, in thousandths of a pixel. -/
def CLEAR : Nat := 2000
/-- The gap between two units, along the tube, in thousandths of a pixel. -/
def MENISCUS : Nat := 2000
/-- How far a collar stands out of a wall, in thousandths of a pixel. -/
def COLLAR : Nat := 3000
/-- How far a tube swells round a unit it carries, on each side, in thousandths of a pixel. -/
def SWELL : Nat := 2000

/-- **The widths of contents** a tube may have, in whole pixels. -/
def LADDER : List Nat := [4, 6, 8, 12, 16]
/-- **The area of a unit**, in square pixels: one amount in every tube. -/
def AREA : Nat := 384

/-- **Every width divides the amount**, so a unit's slot is a whole number of pixels in every
tube. -/
theorem ladder_divides : ∀ c ∈ LADDER, AREA % c = 0 := by decide

/-- **Every width leaves room for a pill**: a slot holds a round meniscus at each end and the gap
to the next, `c + 2 ≤ AREA / c`. -/
theorem ladder_pills : ∀ c ∈ LADDER, c * (c + 2) ≤ AREA := by decide

/-- A unit's slot in a tube whose contents are `bore` thousandths of a pixel wide, in thousandths
of a pixel. -/
def unitLen (bore : Nat) : Nat := if bore = 0 then 0 else AREA * 1000000 / bore

/-- The width of a tube's lumen and of its body, from the width of its contents. -/
def lumen (bore : Nat) : Nat := bore + 2 * CLEAR
def body (bore : Nat) : Nat := bore + 2 * CLEAR + 2 * WALL

/-! ## Marks -/

/-! ## Eases: the kit's springs -/

open Whatwg.Svg.Scene (Easing Spring)

/-- The kit's transition (`Whatwg.Svg.Scene.Transition`): a delay, a duration and an easing, in
thousandths of a beat. Named apart from the view's own `Tools.View.Transition`. -/
abbrev Timing := Whatwg.Svg.Scene.Transition

/-- **The settling ease**: the kit's critically damped spring, let go at rest, that comes to rest
soonest with no swing (`Spring.critical`): a mass that slows into its rest. Its decay over a
twentieth of the beat is `0.691 = e^(−0.37)`, so `ωh = 0.37`, the house's `ω = 7.4` over one
beat; its stops agree with the house's table (`Tools.View.Look.settleTable`) to a thousandth.
The stops are written out, and the guard below holds them to the spring: the spring computes in
rational numbers, whose operations reach `Classical.choice`. -/
def settle : Easing :=
  .stops [0, 54, 170, 305, 437, 554, 653, 734, 798, 849, 888, 918, 940, 957, 970, 979, 986, 992, 995, 998, 1000]

#guard settle == (Spring.critical (691 / 1000) (37 / 100)).easing

/-- The three tones of the pen: a wall, an empty lumen, and contents. -/
inductive Tone where
  | wall | lumen | fluid
deriving DecidableEq, Repr, Inhabited

def Tone.name : Tone → String
  | .wall => "wall" | .lumen => "lumen" | .fluid => "fluid"

/-- **A mark**: a key that joins it across pictures, its layer, the tube whose centreline it
strokes, its width, its tone, its caps, and where it is a dash, the dash's start along the tube
and its length (thousandths of a pixel; a start may lie off either end, where the tube cuts it).
A tube is mixed from its root, so a tube that must stay on what it runs into is given from there,
and `fromEnd` draws it the other way (`Tube.reverse`); a dash is measured along the way drawn.
`move` says how the mark comes into this pose, as the kit's transition in thousandths of the beat:
a delay, a duration and an easing. Its tube may change on a time of its own, `shape`, shared by
every mark on that tube: a unit rides a pipe that bends under it, and keeps to the pipe. -/
structure Mark where
  key : String
  layer : Nat
  tube : Tube
  width : Nat
  tone : Tone
  round : Bool := true
  dash : Option (Int × Nat) := none
  fromEnd : Bool := false
  move : Timing := { ease := settle }
  shape : Option Timing := none
deriving Repr, DecidableEq, Inhabited

/-- The centreline a mark is drawn along. -/
def Mark.drawn (m : Mark) : Tube := if m.fromEnd then m.tube.reverse else m.tube

/-- The layers, drawn in this order. -/
def WALLS : Nat := 0
def LUMENS : Nat := 1
def PLUGS : Nat := 2
def CONTENTS : Nat := 3
def HOLLOWS : Nat := 4

/-- **A tube's body**: its wall and its lumen. A tube that opens to the world is cut square at its
ends; one that is closed has round ends. -/
def bodyOf (key : String) (t : Tube) (fromEnd : Bool := false) (round : Bool := true) : List Mark :=
  [{ key := key ++ ":wall", layer := WALLS, tube := t, width := body t.bore, tone := .wall, fromEnd, round },
   { key := key ++ ":lumen", layer := LUMENS, tube := t, width := lumen t.bore, tone := .lumen, fromEnd, round }]

/-- The dash of a pill in the slot whose front stands `front` along a tube: the round ends stand
inside the slot, a meniscus from the next. -/
def pillDash (t : Tube) (front : Int) : Int × Nat :=
  let u := unitLen t.bore
  (front - u + MENISCUS / 2 + t.bore / 2, u - MENISCUS - t.bore)

/-- **A unit** in the slot whose front stands `front` along the tube (thousandths of a pixel): a
pill. -/
def unitOf (key : String) (t : Tube) (front : Int) : Mark :=
  { key, layer := CONTENTS, tube := t, width := t.bore, tone := .fluid, dash := some (pillDash t front) }

/-- The rim of a promised unit, in thousandths of a pixel. -/
def RIM : Nat := 2000

/-- **A promised unit**, a bubble in the line: the pill's outline, its inside the lumen's tone. -/
def hollowOf (key : String) (t : Tube) (front : Int) : List Mark :=
  [{ key := key ++ ":rim", layer := CONTENTS, tube := t, width := t.bore, tone := .fluid,
     dash := some (pillDash t front) },
   { key := key ++ ":in", layer := HOLLOWS, tube := t, width := t.bore - 2 * RIM, tone := .lumen,
     dash := some (pillDash t front) }]

/-- **A plug** across the lumen from `s` along the tube, `len` long: a closed valve. -/
def plugOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  { key, layer := PLUGS, tube := t, width := lumen t.bore, tone := .wall, round := false,
    dash := some (s, len) }

/-- **A collar** round a tube from `s`, `len` long: a fitting, of the wall's tone, round at its
ends. -/
def collarOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  let w := body t.bore + 2 * COLLAR
  { key, layer := WALLS, tube := t, width := w, tone := .wall,
    dash := some (s + (min len w / 2 : Nat), len - min len w) }

/-! ## Morphs -/

/-- **Two marks mixed** `t` thousandths of the way: the tube by its intrinsic morph, the width and
the dash by the line between them. -/
def Mark.mix (a b : Mark) (t : Nat) : Mark :=
  { a with
    tube := a.tube.mix b.tube t
    width := ((1000 - t) * a.width + t * b.width) / 1000
    dash := match a.dash, b.dash with
      | some (s, l), some (s', l') => some (mixInt s s' t, ((1000 - t) * l + t * l') / 1000)
      | d, _ => d }

/-- A mark shrunk to nothing where it stands: a dash to no length and no width, a tube to its
root. -/
def Mark.gone (m : Mark) : Mark :=
  match m.dash with
  | some (s, l) => { m with dash := some (s + (l / 2 : Nat), 0), width := 0 }
  | none => { m with tube := { m.tube with pieces := m.tube.pieces.map fun _ => Piece.zero } }

/-! ## Writing -/

/-- A dash's gap: longer than any picture's tube. -/
def BIG : Nat := 100000000

/-- A length in thousandths of a pixel, as SVG writes it. -/
def num (n : Int) : String := SvgAttr.numberText (.fixed 3 n)

/-- A tube's centreline as path data. -/
def pathOf (t : Tube) : Path :=
  match t.cubics with
  | [] => (Pen.begin (SvgOut.milli (t.x, t.y))).path
  | c :: rest => ((c :: rest).foldl (fun pen s =>
      pen.curveTo (SvgOut.milli s.p1) (SvgOut.milli s.p2) (SvgOut.milli s.p3))
      (Pen.begin (SvgOut.milli c.p0))).path

def pathText (t : Tube) : String := String.ofList (Path.grammar.print (pathOf t))

/-- The dash pattern and offset of a dash, as text. -/
def dashText (d : Int × Nat) : String × String := (num d.2 ++ " " ++ num BIG, num (-d.1))

/-- **A path** with its attributes and its animations. -/
def pathNode (t : Tube) (cls : String) (width : Nat) (round : Bool) (dash : Option (Int × Nat))
    (anims : List SvgNode) : SvgNode :=
  .element .path
    ([.attr .d (.path (pathOf t)), .className cls, .fill .none, .strokeWidth (.fixed 3 width),
      .strokeLinecap (if round then .round else .butt), .strokeLinejoin .round] ++
     match dash with
     | some d => let (a, o) := dashText d; [.attr .stroke_dasharray a, .attr .stroke_dashoffset o]
     | none => [])
    anims

/-- **A mark as a path**, with its animations. -/
def node (m : Mark) (anims : List SvgNode) : SvgNode :=
  pathNode m.drawn ("tube-" ++ m.tone.name) m.width m.round m.dash anims

/-- The layers' count. -/
def LAYERS : Nat := 5

/-- **A still picture** of `W` by `H` pixels. -/
def still (W H : Nat) (ms : List Mark) : SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view"]
    ((List.range LAYERS).flatMap fun l => (ms.filter (·.layer == l)).map (node · []))

/-- The page's rules for the pen's tones, from the look's ink and ground, and for drawing a
picture one pixel to the pixel where the page has the room. -/
def css : String :=
  ".tube-wall { stroke: color-mix(in srgb, var(--e4-color-ink) 32%, var(--e4-color-ground)); }\n" ++
  ".tube-lumen { stroke: color-mix(in srgb, var(--e4-color-ink) 8%, var(--e4-color-ground)); }\n" ++
  ".tube-fluid { stroke: var(--e4-color-ink); }\n" ++
  "svg.tube-view { display: block; max-width: 100%; height: auto; shape-rendering: geometricPrecision; }\n" ++
  "svg.tube-view[id] { cursor: pointer; }\n"

-- the slots: a pipe of 12 px holds a unit 32 px long, a vessel of 16 px one 24 px long
#guard unitLen 12000 == 32000 && unitLen 16000 == 24000 && unitLen 4000 == 96000
-- a pill in a pipe of 12: its dash 18 px, so 30 px with its round ends, 2 px to the next
#guard pillDash (straight 0 0 0 12000 100000) 100000 == (75000, 18000)

end Tools.View.Tube
