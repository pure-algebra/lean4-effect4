import Tools.View.Tube.Outline
import Tools.View.SvgOut
import Whatwg.Svg.Geometry.Spring

/-!
# Tools.View.Tube.Draw — one pen, one amount, and every transition a morph

**One pen, solid bodies** (the owner's ruling of 2026-10-13, decisions row 370). Every tube is a
solid body, filled in one tone, and its outline is smooth everywhere (`Tools.View.Tube.Outline`).
Its contents are pills of ink stroked along its centreline. **A join carries a meaning.** Two
bodies that meet in one fill share their fluid: a tee or a wye conserves, and its crotch is
rounded wide, as a branch widens into its tree (`Join`, `crotch`), so no join has a kink. Two
bodies kept apart by an air gap of `GAP` share nothing, and each end that faces the gap is round:
a closed valve parts its pipe (`plugOf`), a broadcast's taps stand a gap from their source, each
with its own copy, and the tube below a crossing is parted round the one that passes over (its
`level`, `cutOf`). Every width is a whole, even number of pixels, and a straight run's edges fall
on pixel edges.

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
/-- **An air gap**: the ground between two bodies that share nothing, in thousandths of a pixel. -/
def GAP : Nat := 4000
/-- How long a reducer is, from a pipe's width to a vessel's, in thousandths of a pixel. -/
def REDUCER : Nat := 10000

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

/-- The width of a tube's lumen and of its body, from the width of its contents: the body holds
its contents with the clearance and the wall round them. -/
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

/-- The three tones of the pen: a body, its contents, and the ground an air gap shows. -/
inductive Tone where
  | body | fluid | ground
deriving DecidableEq, Repr, Inhabited

def Tone.name : Tone → String
  | .body => "body" | .fluid => "fluid" | .ground => "ground"

/-- **How a mark is drawn**: stroked along its tube's centreline (contents, a hollow); as a solid
body, its outline filled; as a stretch of its body whose width changes, from its width to `w1`,
with `peak` more eased over `rise` at each end, over its dash (`patchCubics`); or as a parting, the
ground between two round ends of its body across its dash (`partCubics`). -/
inductive Fill where
  | stroke
  | solid
  | stretch (w1 : Nat) (peak : Int) (rise : Nat)
  | part
deriving DecidableEq, Repr, Inhabited



/-- **A mark**: a key that joins it across pictures, its layer, the tube whose centreline it
strokes, its width, its tone, its caps, and where it is a dash, the dash's start along the tube
and its length (thousandths of a pixel; a start may lie off either end, where the tube cuts it).
A tube is mixed from its root, so a tube that must stay on what it runs into is given from there,
and `fromEnd` draws it the other way (`Tube.reverse`); a dash is measured along the way drawn.
`move` says how the mark comes into this pose, as the kit's transition in thousandths of the beat:
a delay, a duration and an easing. Its tube may change on a time of its own, `shape`, shared by
every mark on that tube: a unit rides a pipe that bends under it, and keeps to the pipe. A mark is
stroked, solid or a stretch (`fill`), and stands at a depth (`level`): a tube that passes over
another is drawn after it, with a gap round it. -/
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
  fill : Fill := .stroke
  level : Nat := 0
deriving Repr, DecidableEq, Inhabited

/-- The centreline a mark is drawn along. -/
def Mark.drawn (m : Mark) : Tube := if m.fromEnd then m.tube.reverse else m.tube

/-- The layers of a depth, drawn in this order: the grounds a tube clears round it, the bodies,
the partings that cut them, the contents, the insides of promised units. -/
def HALOS : Nat := 0
def BODIES : Nat := 1
def GAPS : Nat := 2
def CONTENTS : Nat := 3
def HOLLOWS : Nat := 4

/-- **A tube's body**: one solid fill. A tube that opens to the world is cut square at its ends,
off the picture; one that is closed has round ends. A tube that passes over another stands at a
deeper `level`, drawn after it, and the one below is parted round it (`cutOf`). -/
def bodyOf (key : String) (t : Tube) (fromEnd : Bool := false) (round : Bool := true)
    (level : Nat := 0) : List Mark :=
  [{ key := key ++ ":wall", layer := BODIES, tube := t, width := body t.bore, tone := .body, fromEnd,
     round, fill := .solid, level }]

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

/-- **A promised unit**, a bubble in the line: the pill's outline, its inside the body's tone: a ring of ink that the body shows through. -/
def hollowOf (key : String) (t : Tube) (front : Int) : List Mark :=
  [{ key := key ++ ":rim", layer := CONTENTS, tube := t, width := t.bore, tone := .fluid,
     dash := some (pillDash t front) },
   { key := key ++ ":in", layer := HOLLOWS, tube := t, width := t.bore - 2 * RIM, tone := .body,
     dash := some (pillDash t front) }]

/-- **A closed valve**: the pipe parted by an air gap from `s` along the tube, `len` long, its two
ends round and facing each other; nothing passes. Opening it fuses the ends into one body. -/
def plugOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  { key, layer := GAPS, tube := t, width := body t.bore, tone := .ground, round := false,
    dash := some (s, len), fill := .part }

/-- **A crossing's parting**: the body below parted round a body `over` wide that passes over it
at `at_` along the tube, an air gap each side, its ends round. -/
def cutOf (key : String) (t : Tube) (at_ : Int) (over : Nat) : Mark :=
  plugOf key t (at_ - (over / 2 + GAP : Nat)) (over + 2 * GAP)

/-- **A stretch of a body** from `s` along the tube, `len` long, its width from `w0` to `w1` with
`peak` more eased over `rise` at each end: one fill with its body, whose edges it meets on their
tangent. -/
def stretchOf (key : String) (t : Tube) (s : Int) (len w0 w1 : Nat) (peak : Int) (rise : Nat) : Mark :=
  { key, layer := BODIES, tube := t, width := w0, tone := .body, round := false,
    dash := some (s, len), fill := .stretch w1 peak rise }

/-- **A sleeve** round a tube from `s`, `len` long: a fitting, the body standing `COLLAR` out on
each side, eased in and out. -/
def collarOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  stretchOf key t s len (body t.bore) (body t.bore) (2 * COLLAR) (min (len / 3) 4000)

/-- **A reducer** at a tube's start: its body grows from the width `from_` to its own over
`REDUCER`, as a concentric reducer joins a pipe to a wider vessel; at its end (`atEnd`), back down. -/
def reducerOf (key : String) (t : Tube) (from_ : Nat) (atEnd : Bool := false) : Mark :=
  if atEnd then stretchOf key t ((t.length : Int) - REDUCER) REDUCER (body t.bore) from_ 0 0
  else stretchOf key t 0 REDUCER from_ (body t.bore) 0 0

/-- **A vessel between pipes**: its body narrowed at each end by a reducer, from the inlet's width
`inW` and to the outlet's `outW`, over `REDUCER`; the body between them overlaps each by two
pixels, so no seam shows. A pipe that meets it ends round, inside the reducer. -/
def reducedOf (key : String) (t : Tube) (inW outW : Nat) : List Mark :=
  let L := t.length
  bodyOf key (t.cut (REDUCER - 2000) (L - (REDUCER - 2000))) (round := false) ++
    [reducerOf (key ++ ":r0") t inW, reducerOf (key ++ ":r1") t outW (atEnd := true)]

/-- **A solid join**: the branch leaves the parent on its tangent, and they share one fill; its
crotch is rounded (`crotch`). The keys are the two bodies' marks. -/
structure Join where
  key : String
  parent : String
  branch : String
deriving Repr, Inhabited

/-! ## Morphs -/

/-- **Two marks mixed** `t` thousandths of the way: the tube by its intrinsic morph, the width and
the dash by the line between them. -/
def Mark.mix (a b : Mark) (t : Nat) : Mark :=
  { a with
    tube := a.tube.mix b.tube t
    width := ((1000 - t) * a.width + t * b.width) / 1000
    dash := match a.dash, b.dash with
      | some (s, l), some (s', l') => some (mixInt s s' t, ((1000 - t) * l + t * l') / 1000)
      | d, _ => d
    fill := match a.fill, b.fill with
      | .stretch w p r, .stretch w' p' r' =>
        .stretch (((1000 - t) * w + t * w') / 1000) (mixInt p p' t) (((1000 - t) * r + t * r') / 1000)
      | f, _ => f }

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

/-- A point in thousandths of a pixel, written in tenths: a tenth of a pixel is finer than a
screen of twice the density draws. -/
def deci (p : Int × Int) : Point := .fixed 1 ((p.1 + 50) / 100) ((p.2 + 50) / 100)

/-- A tube's centreline as path data. -/
def pathOf (t : Tube) : Path :=
  match t.cubics with
  | [] => (Pen.begin (deci (t.x, t.y))).path
  | c :: rest => ((c :: rest).foldl (fun pen s =>
      pen.curveTo (deci s.p1) (deci s.p2) (deci s.p3))
      (Pen.begin (deci c.p0))).path

def pathText (t : Tube) : String := String.ofList (Path.grammar.print (pathOf t))

/-- The dash pattern and offset of a dash, as text. -/
def dashText (d : Int × Nat) : String × String := (num d.2 ++ " " ++ num BIG, num (-d.1))

/-- **A closed run of cubics** as path data. -/
def closedPath (cs : List Cubic) : Path :=
  match cs with
  | [] => (Pen.begin (deci (0, 0))).path
  | c :: rest => ((c :: rest).foldl (fun pen s =>
      pen.curveTo (deci s.p1) (deci s.p2) (deci s.p3))
      (Pen.begin (deci c.p0))).close.path

def closedText (cs : List Cubic) : String := String.ofList (Path.grammar.print (closedPath cs))

/-- **The outline of a filled mark**: a solid body's, or a stretch's over its dash. -/
def Mark.outline (m : Mark) : List Cubic :=
  match m.fill, m.dash with
  | .stretch w1 peak rise, some (s, len) => patchCubics m.drawn s len m.width w1 peak rise
  | .part, some (s, len) => partCubics m.drawn s len m.width GAP
  | .stretch _ _ _, none | .part, none => []
  | _, _ => bodyCubics m.drawn m.width m.round m.round

/-- **A stroked path** with its attributes and its animations. -/
def pathNode (t : Tube) (cls : String) (width : Nat) (round : Bool) (dash : Option (Int × Nat))
    (anims : List SvgNode) : SvgNode :=
  .element .path
    ([.attr .d (.path (pathOf t)), .className cls, .fill .none, .stroke .currentColor,
      .strokeWidth (.fixed 3 width), .strokeLinecap (if round then .round else .butt),
      .strokeLinejoin .round] ++
     match dash with
     | some d => let (a, o) := dashText d; [.attr .stroke_dasharray a, .attr .stroke_dashoffset o]
     | none => [])
    anims

/-- **A filled path** with its animations. -/
def fillNode (cs : List Cubic) (cls : String) (anims : List SvgNode) : SvgNode :=
  .element .path [.attr .d (.path (closedPath cs)), .className cls, .fill .currentColor] anims

/-- **A mark as a path**, with its animations. -/
def node (m : Mark) (anims : List SvgNode) : SvgNode :=
  match m.fill with
  | .stroke => pathNode m.drawn ("tube-" ++ m.tone.name) m.width m.round m.dash anims
  | _ => fillNode m.outline ("tube-" ++ m.tone.name) anims

/-- The path data of a mark as it stands: its centreline where it is stroked, its outline where
it is filled. -/
def Mark.d (m : Mark) : String :=
  match m.fill with
  | .stroke => pathText m.drawn
  | _ => closedText m.outline

/-- **A join's web** where both its marks stand among `ms`: the crotch between the parent's body
and the branch, or nothing. A web of no size keeps the same commands, so a film can grow it. -/
def Join.web (j : Join) (ms : List Mark) : List Cubic :=
  match ms.find? (·.key == j.parent), ms.find? (·.key == j.branch) with
  | some p, some b =>
    match crotch p.width b.drawn b.width with
    | some cs => cs
    | none => let o := (b.drawn.x, b.drawn.y); [lineC o o, lineC o o, lineC o o]
  | _, _ => [lineC (0, 0) (0, 0), lineC (0, 0) (0, 0), lineC (0, 0) (0, 0)]

/-- The layers' count. -/
def LAYERS : Nat := 5

/-- The deepest level among marks. -/
def depth (ms : List Mark) : Nat := ms.foldl (fun d m => max d m.level) 0

/-- **A still picture** of `W` by `H` pixels: each level in turn, its layers in order, a join's
web with the bodies of its branch's level. -/
def still (W H : Nat) (ms : List Mark) (joins : List Join := []) : SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view"]
    ((List.range (depth ms + 1)).flatMap fun lv => (List.range LAYERS).flatMap fun l =>
      ((ms.filter fun m => m.level == lv && m.layer == l).map (node · [])) ++
      (if l == BODIES then
        (joins.filter fun j => (ms.find? (·.key == j.branch)).any (·.level == lv)).map fun j =>
          fillNode (j.web ms) "tube-body" []
       else []))

/-- The page's rules for the pen's tones, from the look's ink and ground, and for drawing a
picture one pixel to the pixel where the page has the room. Each path takes its tone as `color`,
and fills or strokes with it. -/
def css : String :=
  ".tube-body { color: color-mix(in srgb, var(--e4-color-ink) 34%, var(--e4-color-ground)); }\n" ++
  ".tube-fluid { color: var(--e4-color-ink); }\n" ++
  ".tube-ground { color: var(--e4-color-ground); }\n" ++
  "svg.tube-view { display: block; max-width: 100%; height: auto; shape-rendering: geometricPrecision; }\n" ++
  "svg.tube-view[id] { cursor: pointer; }\n"

-- the slots: a pipe of 12 px holds a unit 32 px long, a vessel of 16 px one 24 px long
#guard unitLen 12000 == 32000 && unitLen 16000 == 24000 && unitLen 4000 == 96000
-- a pill in a pipe of 12: its dash 18 px, so 30 px with its round ends, 2 px to the next
#guard pillDash (straight 0 0 0 12000 100000) 100000 == (75000, 18000)

end Tools.View.Tube
