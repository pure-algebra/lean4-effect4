import Tools.View.Picture

/-!
# The look: every choice of style, as data

A look holds every choice that a picture makes and that no program decides: the colour of each
role, the faces of the type, the weight of each stroke, the form of an edge, and the timing of
motion. The drawing reads a look, and the outputs write it. No other module of the view holds a
colour, a face or a duration.

A look follows the web's standards, so that a picture moves to the web with no framework of its
own (`Tools.View.Tokens` writes and reads them):

- a look is a file of the W3C Design Tokens Community Group's format, 2025.10: colours, dimensions,
  typography, durations and transitions as that format defines them;
- its colours are sRGB, and the web reads them as CSS custom properties;
- an edge's form is a curve of d3-shape (`Curve`);
- an easing is CSS's `linear()` easing function at twenty-one points (`Ease.points`), and the
  nearest cubic Bézier for a tool that reads only `cubic-bezier` (`Ease.bezier`);
- a duration is in milliseconds, as CSS transitions and the token format write it.

The defaults are the dark look: the palette of `paint.h`'s round-3 probe, whose hues passed the
palette validator on their ground (hues-run.txt of the round-3 probe), and the faces of
`paint_faces_open`. Every other look is a token file that changes some of them
(`tools/view/looks/`).
-/

namespace Tools.View

/-! ## Easing -/

/-- An easing: a progress in per mille to an eased progress in per mille. `outBack` overshoots a
little before it settles. `settle` and `spring` are a mass on a damped spring released toward its
rest, so a moving element has weight: `settle` is critically damped, the fastest approach with no
overshoot; `spring` is underdamped, a small overshoot that dies away. -/
inductive Ease where
  | linear | in_ | out | inOut | outBack | settle | spring
deriving Repr, DecidableEq

/-- A critically damped spring released at rest from 0 toward 1, `1 - (1 + ωs)e^(-ωs)` with
`ω = 7.4` over one step, scaled to end at 1; per mille at every twentieth of the step. -/
def settleTable : List Int :=
  [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992, 995, 998, 1000]

/-- An underdamped spring, damping ratio `ζ = 0.7` and `ω = 7.5` over one step, scaled to end at 1:
it overshoots by 4.5% at about three fifths of the step and settles; per mille at every twentieth. -/
def springTable : List Int :=
  [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026, 1019, 1012, 1007, 1003, 1000]

/-- A table read at `p` per mille: the line between its two nearest entries; past its end, 1. -/
def tableAt (t : List Int) (p : Nat) : Int :=
  let a := t.getD (p / 50) 1000
  let b := t.getD (p / 50 + 1) 1000
  a + (b - a) * ((p % 50 : Nat) : Int) / 50

/-- The eased progress at `p` per mille (cubic curves; `outBack` with the usual 1.70158). -/
def Ease.at : Ease → Nat → Int
  | .linear, p => p
  | .in_, p => (p : Int) ^ 3 / 1000000
  | .out, p => 1000 - (1000 - (p : Int)) ^ 3 / 1000000
  | .inOut, p =>
    if p < 500 then 4 * (p : Int) ^ 3 / 1000000 else 1000 - (2 * (1000 - (p : Int))) ^ 3 / 2000000
  | .outBack, p =>
    let q : Int := (p : Int) - 1000
    1000 + 2702 * q ^ 3 / 1000000000 + 1702 * q ^ 2 / 1000000
  | .settle, p => tableAt settleTable p
  | .spring, p => tableAt springTable p

/-- Every easing starts at 0. -/
theorem Ease.at_start (e : Ease) : e.at 0 = 0 := by cases e <;> rfl

/-- Every easing ends at 1. -/
theorem Ease.at_end (e : Ease) : e.at 1000 = 1000 := by cases e <;> rfl

/-- An easing's name in a token file. -/
def Ease.name : Ease → String
  | .linear => "linear" | .in_ => "in" | .out => "out" | .inOut => "inOut" | .outBack => "outBack"
  | .settle => "settle" | .spring => "spring"

/-- The easings, in order. -/
def Ease.all : List Ease := [.linear, .in_, .out, .inOut, .outBack, .settle, .spring]

/-- The easing of a name. -/
def Ease.ofName? (s : String) : Option Ease := Ease.all.find? (·.name == s)

/-- The easing at every twentieth of its progress, per mille: the points of CSS's `linear()`. -/
def Ease.points (e : Ease) : List Int := (List.range 21).map fun i => e.at (i * 50)

/-- `a / b` rounded to the nearest whole number, for a positive `b`. -/
def roundDiv (a b : Int) : Int := (2 * a + b) / (2 * b)

/-- **The nearest cubic Bézier.** `cubic-bezier(1/3, y1, 2/3, y2)` is, in the progress `s`, the
cubic `3·y1·s(1−s)² + 3·y2·s²(1−s) + s³`, linear in the two heights. So the heights that are
nearest the easing's twenty-one points are the least-squares solution of two normal equations,
computed here in whole numbers. The cubic easings (`in_`, `out`, `outBack`) are such cubics, and
come back to within the rounding of their points; the others are the nearest of the family. The
heights are per mille. Each basis term is scaled by `20³`. -/
def Ease.bezier (e : Ease) : Int × Int :=
  let pts := e.points.zipIdx
  let b1 (i : Nat) : Int := 3 * (i : Int) * (20 - (i : Int)) ^ 2
  let b2 (i : Nat) : Int := 3 * (i : Int) ^ 2 * (20 - (i : Int))
  let res (v : Int) (i : Nat) : Int := 8 * v - (i : Int) ^ 3
  let sum (f : Int → Nat → Int) : Int := pts.foldl (fun s (v, i) => s + f v i) 0
  let a11 := sum fun _ i => b1 i * b1 i
  let a12 := sum fun _ i => b1 i * b2 i
  let a22 := sum fun _ i => b2 i * b2 i
  let r1 := sum fun v i => b1 i * res v i
  let r2 := sum fun v i => b2 i * res v i
  let det := a11 * a22 - a12 * a12
  (roundDiv (1000 * (r1 * a22 - r2 * a12)) det, roundDiv (1000 * (a11 * r2 - a12 * r1)) det)

/-! ## Transitions -/

/-- A transition: a delay, a duration and an easing. A look writes them in milliseconds; the
sampler reads them in per mille of one step (`Choreography.norm`). -/
structure Transition where
  delay : Nat := 0
  duration : Nat := 1000
  ease : Ease := .inOut
deriving Repr, DecidableEq

/-- The eased progress of a transition at the moment `t` of a step, both in per mille. -/
def Transition.at (tr : Transition) (t : Nat) : Int :=
  if tr.delay + tr.duration ≤ t then 1000
  else if t ≤ tr.delay then tr.ease.at 0
  else tr.ease.at ((t - tr.delay) * 1000 / tr.duration)

/-- A transition is done at its end. -/
theorem Transition.at_end (tr : Transition) (t : Nat) (h : tr.delay + tr.duration ≤ t) :
    tr.at t = 1000 := by
  simp only [Transition.at, h, if_true]

/-- A transition held inside its step: it starts by the step's end and ends by it. -/
def Transition.within (tr : Transition) : Transition :=
  { tr with delay := min tr.delay 1000, duration := min tr.duration (1000 - min tr.delay 1000) }

/-- A held transition ends by the step's end. -/
theorem Transition.within_end (tr : Transition) : tr.within.delay + tr.within.duration ≤ 1000 := by
  simp only [Transition.within]
  omega

/-- So it is done at the step's end. -/
theorem Transition.within_at_end (tr : Transition) : tr.within.at 1000 = 1000 :=
  tr.within.at_end 1000 tr.within_end

/-- A transition started `d` later, held inside its step. -/
def Transition.after (tr : Transition) (d : Nat) : Transition :=
  ({ tr with delay := tr.delay + d } : Transition).within

/-- A transition started later is done at the step's end too. -/
theorem Transition.after_at_end (tr : Transition) (d : Nat) : (tr.after d).at 1000 = 1000 :=
  Transition.within_at_end _

/-- A transition of milliseconds in per mille of a step of `step` milliseconds. -/
def Transition.per (step : Nat) (tr : Transition) : Transition :=
  { tr with delay := tr.delay * 1000 / step, duration := tr.duration * 1000 / step }

/-! ## The choreography -/

/-- **The choreography**: how long a step lasts, and the transition of each selection, in
milliseconds. At the defaults a step lasts 600 ms. -/
structure Choreography where
  /-- the length of one step, from one frame to the next -/
  step : Nat := 600
  /-- the kept elements move to their new places, and settle there with weight -/
  move : Transition := { duration := 270, ease := .settle }
  /-- the old elements shrink or unwrite -/
  leave : Transition := { duration := 150, ease := .in_ }
  /-- a new or changed line writes itself, cell by cell -/
  write : Transition := { delay := 180, duration := 180, ease := .linear }
  /-- the delay from one new line to the next -/
  stagger : Nat := 36
  /-- when the new parts of a graph start, after the room is made -/
  enterFrom : Nat := 180
  /-- a new edge draws from its source toward its target -/
  draw : Transition := { duration := 132, ease := .out }
  /-- the box at its end expands out, on a spring -/
  expand : Transition := { duration := 216, ease := .spring }
deriving Repr, DecidableEq

/-- The choreography in per mille of its step, as the sampler reads it. -/
def Choreography.norm (c : Choreography) : Choreography :=
  { step := 1000, move := c.move.per c.step, leave := c.leave.per c.step, write := c.write.per c.step,
    stagger := c.stagger * 1000 / c.step, enterFrom := c.enterFrom * 1000 / c.step,
    draw := c.draw.per c.step, expand := c.expand.per c.step }

/-! ## Colour, type, strokes and the form of an edge -/

/-- A colour of sRGB, as `0xRRGGBB`. -/
abbrev Rgb := Nat

/-- The colour of each role. -/
structure Palette where
  ground : Rgb
  ink : Rgb
  rule : Rgb
  host : Rgb
  failure : Rgb
  resource : Rgb
deriving Repr, DecidableEq

/-- The colour of a role. -/
def Palette.of (p : Palette) : Role → Rgb
  | .ground => p.ground | .ink => p.ink | .rule => p.rule
  | .host => p.host | .failure => p.failure | .resource => p.resource

/-- The roles, in order, with their names in a token file. -/
def Role.all : List Role := [.ground, .ink, .rule, .host, .failure, .resource]

/-- A role's name in a token file and in CSS. -/
def Role.tokenName : Role → String
  | .ground => "ground" | .ink => "ink" | .rule => "rule"
  | .host => "host" | .failure => "failure" | .resource => "resource"

/-- Whether a look is dark or light: CSS's `color-scheme`. -/
inductive Scheme where
  | dark | light
deriving Repr, DecidableEq

/-- The scheme's CSS keyword. -/
def Scheme.name : Scheme → String
  | .dark => "dark" | .light => "light"

/-- A face of the type: its families in order of preference, its size in thousandths of a
logical pixel, its weight (100 to 900, as CSS and the token format write it), and whether it
is italic. The data face's size is the one whose advance is one cell: `paint.h` measures it
from the cell, and the size here is its value in Menlo, for the web. -/
structure Font where
  family : List String
  size : Nat
  weight : Nat := 400
  italic : Bool := false
deriving Repr, DecidableEq

/-- The four faces. -/
structure Faces where
  data : Font
  name : Font
  label : Font
  title : Font
deriving Repr, DecidableEq

/-- A face's font. -/
def Faces.of (f : Faces) : Face → Font
  | .data => f.data | .name => f.name | .label => f.label | .title => f.title

/-- The faces, in order. -/
def Face.all : List Face := [.data, .name, .label, .title]

/-- A face's name in a token file and in CSS. -/
def Face.tokenName : Face → String
  | .data => "data" | .name => "name" | .label => "label" | .title => "title"

/-- The form of an edge between two ranks, after d3-shape's curves:

- `bumpY`: d3's `curveBumpY`, the vertical link: one cubic, vertical at both ends;
- `linear`: d3's `curveLinear`, a straight segment;
- `stepY`: d3's `curveStep` with its axes exchanged: down, across at the middle, down. -/
inductive Curve where
  | bumpY | linear | stepY
deriving Repr, DecidableEq

/-- A curve's name in a token file. -/
def Curve.name : Curve → String
  | .bumpY => "bumpY" | .linear => "linear" | .stepY => "stepY"

/-- The curve of a name. -/
def Curve.ofName? (s : String) : Option Curve := [Curve.bumpY, .linear, .stepY].find? (·.name == s)

/-- The weight of each stroke, in logical pixels. -/
structure Strokes where
  /-- an edge of a graph -/
  edge : Nat := 1
  /-- the frame of a box -/
  frame : Nat := 1
  /-- a rule of the page -/
  rule : Nat := 1
deriving Repr, DecidableEq

/-! ## The written forms of a look's values -/

/-- A colour's six hexadecimal digits, `rrggbb`. -/
def Rgb.hex6 (c : Rgb) : String :=
  let ds := Nat.toDigits 16 (c % 0x1000000)
  String.ofList (List.replicate (6 - ds.length) '0' ++ ds)

/-- A colour as CSS and the token format write it: `#rrggbb`. -/
def Rgb.css (c : Rgb) : String := "#" ++ c.hex6

/-- A number of `10^-places` units as a decimal with no trailing zero: `decimal 54 3` is
`0.054`, `decimal 13288 3` is `13.288`, `decimal 1000 3` is `1`. -/
def decimal (v : Int) (places : Nat) : String :=
  let unit := 10 ^ places
  let a := v.natAbs
  let frac := toString (a % unit + unit) |>.drop 1 |>.toString
  let frac := (frac.toList.reverse.dropWhile (· == '0')).reverse
  (if v < 0 then "-" else "") ++ toString (a / unit) ++ (if frac.isEmpty then "" else "." ++ String.ofList frac)

/-- The generic families of CSS, written without quotes. -/
def genericFamilies : List String :=
  ["serif", "sans-serif", "monospace", "cursive", "fantasy", "system-ui", "ui-serif", "ui-sans-serif",
    "ui-monospace", "ui-rounded"]

/-- A font's families as a CSS list: a name with a space in single quotes, so that the list
stands inside an attribute's double quotes. -/
def Font.cssFamily (f : Font) : String :=
  ", ".intercalate (f.family.map fun n =>
    if genericFamilies.contains n || !n.contains ' ' then n else "'" ++ n ++ "'")

/-- A font's size in logical pixels, as a decimal. -/
def Font.px (f : Font) : String := decimal f.size 3

/-- A font's style, as CSS writes it. -/
def Font.style (f : Font) : String := if f.italic then "italic" else "normal"

/-- An easing as CSS's `linear()` easing function at its twenty-one points. -/
def Ease.css (e : Ease) : String := "linear(" ++ ", ".intercalate (e.points.map (decimal · 3)) ++ ")"

/-- A palette with one role's colour replaced. -/
def Palette.set (p : Palette) (role : Role) (c : Rgb) : Palette :=
  match role with
  | .ground => { p with ground := c } | .ink => { p with ink := c } | .rule => { p with rule := c }
  | .host => { p with host := c } | .failure => { p with failure := c } | .resource => { p with resource := c }

/-- Faces with one face replaced. -/
def Faces.set (fs : Faces) (face : Face) (f : Font) : Faces :=
  match face with
  | .data => { fs with data := f } | .name => { fs with name := f }
  | .label => { fs with label := f } | .title => { fs with title := f }

/-! ## The look -/

/-- **A look.** The defaults are the dark look. -/
structure Look where
  name : String := "dark"
  description : String := "The dark ground and the black-and-white base of the native view."
  scheme : Scheme := .dark
  palette : Palette := ⟨0x14110d, 0xf3f4f6, 0x45433f, 0xc0851f, 0xbd3931, 0x359b75⟩
  /-- whether a role of an agent (the host, a failure, a resource) takes its hue; with the hue
  off it is drawn in the ink (`Look.color`) -/
  hue : Bool := false
  /-- the value of the rule's tone in the band behind a lit row or box, per mille -/
  band : Nat := 500
  faces : Faces := {
    data := { family := ["Menlo", "DejaVu Sans Mono", "monospace"], size := 13288 }
    name := { family := ["Georgia", "Charter", "serif"], size := 15000 }
    label := { family := ["Georgia", "Charter", "serif"], size := 13500, italic := true }
    title := { family := ["Georgia", "Charter", "serif"], size := 20000 } }
  strokes : Strokes := {}
  /-- the form of an edge between ranks -/
  curve : Curve := .bumpY
  /-- how far each control of a `bumpY` edge reaches along its drop, per mille of the drop: 500 is
  d3's bump, each control at the middle; 0 is a straight segment -/
  reach : Nat := 500
  motion : Choreography := {}
deriving Repr, DecidableEq

/-- **The colour a role is drawn in**: its own, or the ink for a role of an agent with the hue
off. The base is black and white: this is `paint__source`'s rule (`paint.h`, P9), stated once
for every output. -/
def Look.color (L : Look) (role : Role) : Rgb :=
  match role with
  | .host | .failure | .resource => if L.hue then L.palette.of role else L.palette.ink
  | _ => L.palette.of role

end Tools.View
