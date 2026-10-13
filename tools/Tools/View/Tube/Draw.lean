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

**One proportion** (the owner's choice of 2026-10-13, from a sheet of ratios). Every size is
read from the line: a body's `LINE` is 2 px, as the docs' edges weigh; contents stand a `MARGIN`
of one and a half lines inside it; a unit is a circle `UNIT` 10 px across, the radio button's
proportion 2 : 3 : 10. The bodies' widths step by √2 (`WIDTHS`: 10, 14, 20, 28), so two bodies of
one step hold as much as one of the next, as Leonardo's rule has a tree's branches carry the
area of their trunk (`widths_double`).

**One amount.** A unit has one amount, `AREA` square pixels, the slot of a circle and its
`MENISCUS`: in a tube whose contents are `c` pixels wide its slot is `AREA / c` long. Every width
of the ladder divides the area (`ladder_divides`), so every slot is a whole number of pixels. A
unit is a circle where its tube's bore holds one (`contents`), and in a narrower bore a pill of
the same slot, a liquid plug with a round meniscus at each end, as a plug of liquid stands in a
capillary (Bretherton, "The motion of long bubbles in tubes", 1961); every width of the ladder
leaves room for a whole pill in its slot (`ladder_pills`). A unit that passes from a narrow tube
into a wide one shortens to its circle, as water does.

**Every transition a morph, timed.** A mark says how it comes into its pose with the kit's
`Transition` (`Mark.move`, `Mark.shape`), so a cause moves before its effect. How a picture
becomes the next is `Tools.View.Tube.Motion`.
-/

namespace Tools.View.Tube
open Tools.View Whatwg.Html
open Whatwg.Svg.Value (Decimal Pen Point Path)

/-! ## The pen and the amount -/

/-- **The line** round a body, in thousandths of a pixel: two pixels, the weight of the docs'
edges. Every other size is read from it. -/
def LINE : Nat := 2000
/-- The margin between the contents and the inside of the line, in thousandths of a pixel: one
line and a half. -/
def MARGIN : Nat := 3000
/-- **A unit's width**, in thousandths of a pixel: a circle five lines across. -/
def UNIT : Nat := 10000
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

/-- **The widths of contents** a tube may have, in whole pixels: the widest is a unit's circle. -/
def LADDER : List Nat := [4, 6, 8, 10]
/-- **The area of a unit**, in square pixels: one amount in every tube, a circle's slot,
`UNIT · (UNIT + MENISCUS)`. -/
def AREA : Nat := 120

/-- **The widths of bodies**, in whole pixels, a step of √2 apart: a thin strut, a fine tube, a
pipe, a vessel. -/
def WIDTHS : List Nat := [10, 14, 20, 28]

/-- **Two bodies of one step hold one of the next**, within one in forty: the squares of the
widths double, as Leonardo's rule has two branches carry their trunk's area. -/
theorem widths_double : (WIDTHS.zip WIDTHS.tail).all fun (a, b) =>
    2 * a * a * 40 ≤ b * b * 41 && b * b * 40 ≤ 2 * a * a * 41 := by decide

/-- A circle's slot is the amount: the unit and the meniscus to the next. -/
theorem area_circle : AREA * 1000000 = UNIT * (UNIT + MENISCUS) := by decide

/-- **Every width divides the amount**, so a unit's slot is a whole number of pixels in every
tube. -/
theorem ladder_divides : ∀ c ∈ LADDER, AREA % c = 0 := by decide

/-- **Every width leaves room for a pill**: a slot holds a round meniscus at each end and the gap
to the next, `c + 2 ≤ AREA / c`. -/
theorem ladder_pills : ∀ c ∈ LADDER, c * (c + 2) ≤ AREA := by decide

/-- **The width of a tube's contents**, in thousandths of a pixel: its bore, up to a unit's
circle. -/
def contents (bore : Nat) : Nat := min bore UNIT

/-- A unit's slot in a tube whose bore is `bore` thousandths of a pixel, in thousandths of a
pixel. -/
def unitLen (bore : Nat) : Nat := if contents bore = 0 then 0 else AREA * 1000000 / contents bore

/-- **The width of a tube's body**, from its bore: the margin and the line round it. -/
def body (bore : Nat) : Nat := bore + 2 * MARGIN + 2 * LINE

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

/-- The tones of the pen: a body, its contents, the ground an air gap shows, and a body's casing,
its interior's path filled and stroked a `LINE` round in ink. -/
inductive Tone where
  | body | fluid | ground | casing
deriving DecidableEq, Repr, Inhabited

def Tone.name : Tone → String
  | .body => "body" | .fluid => "fluid" | .ground => "ground" | .casing => "casing"

/-- **How a mark is drawn**: stroked along its tube's centreline (contents, a hollow); as a solid
body, its outline filled; as a stretch of a body over its dash whose width is `top` along its
middle and eases over `rise` from its own width at its start and to `w1` at its end
(`patchCubics`); as a parting, the ground between two round ends of its body across its dash
(`partCubics`); or as a strut, a body all ink, which carries nothing (`ink`). -/
inductive Fill where
  | stroke
  | solid
  | stretch (w1 : Nat) (top : Nat) (rise : Nat)
  | part
  | ink
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
another is drawn after it. `round` is the cap of its ends; `roundStart`, where given, the cap of
its start alone, as a pipe that ends inside a vessel is cut there and round at its other end. -/
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
  roundStart : Option Bool := none
deriving Repr, DecidableEq, Inhabited

/-- The centreline a mark is drawn along. -/
def Mark.drawn (m : Mark) : Tube := if m.fromEnd then m.tube.reverse else m.tube

/-- The layers of a depth, drawn in this order, as the docs' figures draw a node, a frame of ink
round a ground: the grounds a tube clears round it, the bodies in ink, their interiors in ground a
`LINE` inside them, the partings that cut them with their rings, the contents, the insides of
promised units. Where bodies meet, every ink is laid before every interior, so a join's outline
is the one line round the joined bodies. -/
def HALOS : Nat := 0
def BODIES : Nat := 1
def INTERIORS : Nat := 2
def GAPS : Nat := 3
def CONTENTS : Nat := 4
def HOLLOWS : Nat := 5

/-- **A tube's body**: one solid fill. A tube that opens to the world is cut square at its ends,
off the picture; one that is closed has round ends. A tube that passes over another stands at a
deeper `level`, drawn after it, and the one below is parted round it (`cutOf`). -/
def bodyOf (key : String) (t : Tube) (fromEnd : Bool := false) (round : Bool := true)
    (level : Nat := 0) (roundStart : Option Bool := none) : List Mark :=
  [{ key := key ++ ":wall", layer := BODIES, tube := t, width := body t.bore, tone := .body, fromEnd,
     round, fill := .solid, level, roundStart }]

/-- The dash of a pill in the slot whose front stands `front` along a tube: the round ends stand
inside the slot, a meniscus from the next. -/
def pillDash (t : Tube) (front : Int) : Int × Nat :=
  let u := unitLen t.bore
  let c := contents t.bore
  (front - u + MENISCUS / 2 + c / 2, u - MENISCUS - c)

/-- **A unit** in the slot whose front stands `front` along the tube (thousandths of a pixel): a
circle, a dash of no length with round ends, where the bore holds one, else a pill. -/
def unitOf (key : String) (t : Tube) (front : Int) : Mark :=
  { key, layer := CONTENTS, tube := t, width := contents t.bore, tone := .fluid,
    dash := some (pillDash t front) }

/-- **A promised unit**, a bubble in the line: the unit's outline a `LINE` of ink, its inside the
ground, as a hollow node of the docs' figures. -/
def hollowOf (key : String) (t : Tube) (front : Int) : List Mark :=
  [{ key := key ++ ":rim", layer := CONTENTS, tube := t, width := contents t.bore, tone := .fluid,
     dash := some (pillDash t front) },
   { key := key ++ ":in", layer := HOLLOWS, tube := t, width := contents t.bore - 2 * LINE,
     tone := .ground, dash := some (pillDash t front) }]

/-- **A closed valve**: the pipe parted by an air gap from `s` along the tube, `len` long, its two
ends round and facing each other; nothing passes. Opening it fuses the ends into one body. -/
def plugOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  { key, layer := GAPS, tube := t, width := body t.bore, tone := .ground, round := false,
    dash := some (s, len), fill := .part }

/-- **A crossing's parting**: the body below parted round a body `over` wide that passes over it
at `at_` along the tube, an air gap each side, its ends round. -/
def cutOf (key : String) (t : Tube) (at_ : Int) (over : Nat) : Mark :=
  plugOf key t (at_ - (over / 2 + GAP : Nat)) (over + 2 * GAP)

/-- **A stretch of a body** from `s` along the tube, `len` long, `top` wide along its middle and
eased over `rise` from `w0` at its start and to `w1` at its end: one fill with its body, whose
edges it meets on their tangent. -/
def stretchOf (key : String) (t : Tube) (s : Int) (len w0 w1 top rise : Nat) : Mark :=
  { key, layer := BODIES, tube := t, width := w0, tone := .body, round := false,
    dash := some (s, len), fill := .stretch w1 top rise }

/-- **A sleeve** round a tube from `s`, `len` long: a fitting, the body standing `COLLAR` out on
each side, eased in and out. -/
def collarOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  stretchOf key t s len (body t.bore) (body t.bore) (body t.bore + 2 * COLLAR) (min (len / 3) 4000)

/-- How long a reducer is between two widths: twice the change, and at least `REDUCER`, so its
side slopes by no more than one in four. -/
def reducerLen (a b : Nat) : Nat := max REDUCER (2 * (max a b - min a b))

/-- **A vessel between pipes**: one stretch, its body's width along its middle and eased at each
end by a reducer to the inlet's width `inW` and the outlet's `outW`, so its outline is one smooth
line with no seam. A pipe that meets it is cut square and runs `INTO` it (`into`). -/
def reducedOf (key : String) (t : Tube) (inW outW : Nat) : List Mark :=
  [stretchOf (key ++ ":wall") t 0 t.length inW outW (body t.bore)
    (max (reducerLen inW (body t.bore)) (reducerLen outW (body t.bore)))]

/-- How far a pipe runs into the reducer of the vessel it meets, so its interior and the reducer's
overlap, and its square corners stand inside the reducer's outline, in thousandths of a pixel. -/
def INTO : Nat := 6000

/-- **A pipe that meets a vessel**: the tube run `INTO` on past its end (`atEnd`) or back before
its start, straight on its tangent. -/
def into (t : Tube) (atEnd : Bool) : Tube :=
  if atEnd then { t with pieces := t.pieces ++ [⟨INTO, 0⟩] }
  else
    let p := along (t.x, t.y) (-(INTO : Int)) (dir t.head)
    { t with x := p.1, y := p.2, pieces := ⟨INTO, 0⟩ :: t.pieces }

/-- **A solid join**: the branch leaves the parent on its tangent, and they share one fill; its
crotch is rounded (`crotch`). The keys are the two bodies' marks. -/
structure Join where
  key : String
  parent : String
  branch : String
  /-- Where given, a second arm that leaves the branch's start on its heading and turns the
  other way: the crotch is between the two arms (`fork`), and `parent` is only what they leave. -/
  sibling : Option String := none
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
        .stretch (((1000 - t) * w + t * w') / 1000) (((1000 - t) * p + t * p') / 1000)
          (((1000 - t) * r + t * r') / 1000)
      | f, _ => f }

/-- A mark shrunk to nothing where it stands: a dash to no length and no width, a tube to its
root and no width, so a tube grows from its root in length and in width at once, as a branch
does. -/
def Mark.gone (m : Mark) : Mark :=
  match m.dash with
  | some (s, l) => { m with dash := some (s + (l / 2 : Nat), 0), width := 0 }
  | none => { m with tube := { m.tube with pieces := m.tube.pieces.map fun _ => Piece.zero }, width := 0 }

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

/-- **A mark's interior**: a filled mark a `LINE` narrower on each side, in the ground. -/
def Mark.inner (m : Mark) : Mark :=
  { m with key := m.key ++ ":in", layer := INTERIORS, tone := .ground, width := m.width - 2 * LINE,
           fill := match m.fill with | .stretch w1 p r => .stretch (w1 - 2 * LINE) (p - 2 * LINE) r | f => f }

/-- **The outline of a filled mark**: a solid body's, or a stretch's over its dash. -/
def Mark.outline (m : Mark) : List Cubic :=
  match m.fill, m.dash with
  | .stretch w1 top rise, some (s, len) =>
    patchCubics m.drawn s len m.width w1 top rise (m.roundStart.getD false) m.round
  | .part, some (s, len) => partCubics m.drawn s len m.width GAP
  | .stretch _ _ _, none | .part, none => []
  | _, _ => bodyCubics m.drawn m.width (m.roundStart.getD m.round) m.round

/-- **A run of closed loops** as path data. -/
def loopsPath (ls : List (List Cubic)) : Path :=
  let pen := ls.foldl (fun (pen : Option Pen) cs =>
    match cs with
    | [] => pen
    | c :: rest =>
      let start := match pen with
        | none => Pen.begin (deci c.p0)
        | some p => p.moveTo (deci c.p0)
      some ((c :: rest).foldl (fun pen s => pen.curveTo (deci s.p1) (deci s.p2) (deci s.p3)) start).close)
    none
  (pen.getD (Pen.begin (deci (0, 0)))).path

/-- **What a mark draws**: each of its elements, its layer, its tone, and whether it is filled.
A stroked mark is one stroke; a filled one is its interior's path twice, first cased (filled and
stroked a `LINE` round in ink, so its edge stands where the body's does) with the bodies, then
filled with the ground with the interiors; a parting is its ground and its rings of ink. -/
structure Part where
  layer : Nat
  tone : Tone
  filled : Bool
  /-- The path data of the element at a state of the mark. -/
  d : Mark → Path

def Mark.parts (m : Mark) : List Part :=
  match m.fill with
  | .stroke => [⟨m.layer, m.tone, false, fun s => pathOf s.drawn⟩]
  | .part =>
    [⟨GAPS, .ground, true, fun s => closedPath s.outline⟩,
     ⟨GAPS, .body, true, fun s => match s.dash with
       | some (a, len) => loopsPath (ringCubics s.drawn a len s.width GAP LINE)
       | none => loopsPath []⟩]
  | .ink => [⟨m.layer, .casing, true, fun s => closedPath s.inner.outline⟩]
  | _ =>
    [⟨m.layer, .casing, true, fun s => closedPath s.inner.outline⟩,
     ⟨INTERIORS, .ground, true, fun s => closedPath s.inner.outline⟩]

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

/-- **A filled path** from its path data, with its animations. -/
def fillPath (d : Path) (cls : String) (anims : List SvgNode) : SvgNode :=
  .element .path [.attr .d (.path d), .className cls, .fill .currentColor] anims

def fillNode (cs : List Cubic) (cls : String) (anims : List SvgNode) : SvgNode :=
  .element .path [.attr .d (.path (closedPath cs)), .className cls, .fill .currentColor] anims

/-- **A path defined once** under an identifier, with its animations, drawn by `useOf`: a body's
casing and its interior are one path drawn twice. -/
def pathDef (ident : String) (d : Path) (anims : List SvgNode) : SvgNode :=
  .element .path [.ident ident, .attr .d (.path d)] anims

def useOf (ident cls : String) : SvgNode := .element .use [.attr .href ("#" ++ ident), .className cls] []

/-- Whether a mark is drawn as a cased body. -/
def Mark.cased (m : Mark) : Bool := match m.fill with | .solid | .stretch _ _ _ | .ink => true | _ => false

/-- **One element of a mark**, as it stands, with its animations. -/
def partNode (p : Part) (m : Mark) (anims : List SvgNode) : SvgNode :=
  if p.filled then fillPath (p.d m) ("tube-" ++ p.tone.name) anims
  else pathNode m.drawn ("tube-" ++ p.tone.name) m.width m.round m.dash anims

/-- **A mark as a path**: its first element. -/
def node (m : Mark) (anims : List SvgNode) : SvgNode :=
  match m.parts with
  | p :: _ => partNode p m anims
  | [] => pathNode m.drawn "tube-body" m.width m.round m.dash anims

/-- The path data of a mark as it stands: its first element's. -/
def Mark.d (m : Mark) : String :=
  match m.parts with
  | p :: _ => String.ofList (Path.grammar.print (p.d m))
  | [] => pathText m.drawn

/-- **A join's web** where both its marks stand among `ms`: the crotch between the parent's body
and the branch, inset by `grow` for its interior, or nothing. A web of no size keeps the same
commands, so a film can grow it. -/
def Join.web (j : Join) (ms : List Mark) (grow : Nat := 0) : List Cubic :=
  match j.sibling with
  | some sk =>
    match ms.find? (·.key == j.branch), ms.find? (·.key == sk) with
    | some b, some c =>
      match fork b.drawn c.drawn b.width c.width grow with
      | some cs => cs
      | none => noFork (b.drawn.x, b.drawn.y)
    | _, _ => noFork (0, 0)
  | none =>
  match ms.find? (·.key == j.parent), ms.find? (·.key == j.branch) with
  | some p, some b =>
    -- how far the parent runs past the branch's start, along its heading there
    let pt := p.drawn
    let d := dir pt.head
    let along_ : Int := ((b.drawn.x - pt.x) * d.1 + (b.drawn.y - pt.y) * d.2) / ONE
    let room : Int := (pt.length : Int) - along_
    match crotch p.width b.drawn b.width grow room with
    | some cs => cs
    | none => noWeb (b.drawn.x, b.drawn.y)
  | _, _ => noWeb (0, 0)

/-- A join's two elements: its web's interior cased with the bodies, and filled with the
interiors. -/
def Join.parts (j : Join) : List (Nat × Tone × (List Mark → Path)) :=
  [(BODIES, .casing, fun ms => closedPath (j.web ms LINE)),
   (INTERIORS, .ground, fun ms => closedPath (j.web ms LINE))]

/-- The layers' count. -/
def LAYERS : Nat := 6

/-- The deepest level among marks. -/
def depth (ms : List Mark) : Nat := ms.foldl (fun d m => max d m.level) 0

/-- **A still picture** of `W` by `H` pixels: each level in turn, its layers in order, each
mark's elements in their layers, a join's web and its interior with the bodies of its branch's
level. -/
def still (W H : Nat) (ms : List Mark) (joins : List Join := []) : SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view"]
    ((List.range (depth ms + 1)).flatMap fun lv => (List.range LAYERS).flatMap fun l =>
      ((ms.filter (·.level == lv)).flatMap fun m =>
        (m.parts.filter (·.layer == l)).map fun p => partNode p m []) ++
      ((joins.filter fun j => (ms.find? (·.key == j.branch)).any (·.level == lv)).flatMap fun j =>
        (j.parts.filter (·.1 == l)).map fun (_, tone, d) => fillPath (d ms) ("tube-" ++ tone.name) []))

/-- The page's rules for the pen's tones, from the look's ink and ground, as the docs' figures:
ink and ground and nothing between. Each path takes its tone as `color`, and fills or strokes
with it. -/
def css : String :=
  ".tube-body { color: var(--e4-color-ink); }\n" ++
  ".tube-fluid { color: var(--e4-color-ink); }\n" ++
  ".tube-ground { color: var(--e4-color-ground); }\n" ++
  "use.tube-ground { fill: currentColor; stroke: none; }\n" ++
  ".tube-casing { color: var(--e4-color-ink); fill: currentColor; stroke: currentColor; " ++
  "stroke-width: " ++ toString (2 * LINE / 1000) ++ "px; stroke-linejoin: round; }\n" ++
  "svg.tube-view { display: block; max-width: 100%; height: auto; shape-rendering: geometricPrecision; }\n" ++
  "svg.tube-view[id] { cursor: pointer; }\n"

-- the slots: a pipe's bore of 10 px and a vessel's of 18 hold a circle in 12 px, a fine tube's
-- bore of 4 a pill in 30
#guard unitLen 10000 == 12000 && unitLen 18000 == 12000 && unitLen 4000 == 30000
-- a circle in a pipe: a dash of no length, centred 6 px behind its slot's front
#guard pillDash (straight 0 0 0 10000 100000) 100000 == (94000, 0)
-- a pill in a fine tube: its dash 24 px, so 28 px with its round ends, 2 px to the next
#guard pillDash (straight 0 0 0 4000 100000) 100000 == (73000, 24000)
-- the page's casing stroke is two lines wide
#guard (css.splitOn "stroke-width: 4px").length == 2

end Tools.View.Tube
