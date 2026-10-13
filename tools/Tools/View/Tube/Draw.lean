import Tools.View.Tube.Form
import Tools.View.SvgOut

/-!
# Tools.View.Tube.Draw — one pen, one amount, and every transition a morph

**One pen.** Every mark is a tube's centreline stroked: the wall, the lumen inside it, a plug in
the lumen, a collar round it, a unit of its contents. A tube is drawn as three strokes of one path,
as a cartographer draws a road with its casing: every wall first, then every lumen, then the
plugs and the contents (`Mark.layer`). Where two tubes meet, the later lumen covers the earlier
walls, so a junction is one open lumen and needs no shape of its own. The wall is `WALL` thick
and the lumen keeps `CLEAR` round the contents, whatever the tube.

**One amount.** A unit of contents has one area, `AREA` square pixels, in every tube: in a tube
whose contents are `c` pixels wide it is `AREA / c` long. Every width of the ladder divides the
area (`ladder_divides`), so every unit is a whole number of pixels long, and a unit that passes
from a narrow tube into a wide one shortens as water does, by continuity. Units stand a
`MENISCUS` apart, so they are counted.

**Every transition a morph.** A picture is a list of marks with keys. Between two pictures each
mark is mixed with the mark of its key (`Mark.mix`): its tube by the intrinsic morph
(`Tube.mix`), its width and its place on the tube by the line between them. A mark with no
partner retracts to its root. The animator samples the mix at eased moments and writes, for each
attribute that changes, one SVG `animate` with the samples as its values (`film`); WebKit
interpolates no CSS `d`, so the path's samples go to SMIL.
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
def COLLAR : Nat := 2500

/-- **The widths of contents** a tube may have, in whole pixels. -/
def LADDER : List Nat := [4, 6, 8, 12, 16, 24, 32, 48]
/-- **The area of a unit**, in square pixels: one amount in every tube. -/
def AREA : Nat := 192

/-- **Every width divides the amount**, so a unit is a whole number of pixels long in every tube. -/
theorem ladder_divides : ∀ c ∈ LADDER, AREA % c = 0 := by decide

/-- A unit's length in a tube whose contents are `bore` thousandths of a pixel wide, in thousandths
of a pixel. -/
def unitLen (bore : Nat) : Nat := if bore = 0 then 0 else AREA * 1000000 / bore

/-- The width of a tube's lumen and of its body, from the width of its contents. -/
def lumen (bore : Nat) : Nat := bore + 2 * CLEAR
def body (bore : Nat) : Nat := bore + 2 * CLEAR + 2 * WALL

/-! ## Marks -/

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
and `fromEnd` draws it the other way (`Tube.reverse`); a dash is measured along the way drawn. -/
structure Mark where
  key : String
  layer : Nat
  tube : Tube
  width : Nat
  tone : Tone
  round : Bool := true
  dash : Option (Int × Nat) := none
  fromEnd : Bool := false
deriving Repr, DecidableEq, Inhabited

/-- The centreline a mark is drawn along. -/
def Mark.drawn (m : Mark) : Tube := if m.fromEnd then m.tube.reverse else m.tube

/-- The layers, drawn in this order. -/
def WALLS : Nat := 0
def LUMENS : Nat := 1
def PLUGS : Nat := 2
def CONTENTS : Nat := 3
def HOLLOWS : Nat := 4

/-- **A tube's body**: its wall and its lumen. -/
def bodyOf (key : String) (t : Tube) (fromEnd : Bool := false) : List Mark :=
  [{ key := key ++ ":wall", layer := WALLS, tube := t, width := body t.bore, tone := .wall, fromEnd },
   { key := key ++ ":lumen", layer := LUMENS, tube := t, width := lumen t.bore, tone := .lumen, fromEnd }]

/-- **A unit** whose front stands `front` along the tube (thousandths of a pixel): a dash as long
as the amount, less the meniscus. -/
def unitOf (key : String) (t : Tube) (front : Int) : Mark :=
  let u := unitLen t.bore
  { key, layer := CONTENTS, tube := t, width := t.bore, tone := .fluid, round := false
    dash := some (front - u + MENISCUS / 2, u - MENISCUS) }

/-- **A hollow unit**, a promise of contents: the unit's outline, its inside the lumen's tone. -/
def hollowOf (key : String) (t : Tube) (front : Int) : List Mark :=
  let u := unitLen t.bore
  let rim : Nat := 1500
  [{ key := key ++ ":rim", layer := CONTENTS, tube := t, width := t.bore, tone := .fluid,
     round := false, dash := some (front - u + MENISCUS / 2, u - MENISCUS) },
   { key := key ++ ":in", layer := HOLLOWS, tube := t, width := t.bore - 2 * rim, tone := .lumen,
     round := false, dash := some (front - u + MENISCUS / 2 + rim, u - MENISCUS - 2 * rim) }]

/-- **A plug** across the lumen from `s` along the tube, `len` long: a closed valve. -/
def plugOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  { key, layer := PLUGS, tube := t, width := lumen t.bore, tone := .wall, round := false,
    dash := some (s, len) }

/-- **A collar** round a tube from `s`, `len` long: a fitting, of the wall's tone. -/
def collarOf (key : String) (t : Tube) (s : Int) (len : Nat) : Mark :=
  { key, layer := WALLS, tube := t, width := body t.bore + 2 * COLLAR, tone := .wall, round := false,
    dash := some (s, len) }

/-! ## Morphs between pictures -/

/-- **Two marks mixed** `t` thousandths of the way: the tube by its intrinsic morph, the width and
the dash by the line between them. -/
def Mark.mix (a b : Mark) (t : Nat) : Mark :=
  { a with
    tube := a.tube.mix b.tube t
    width := ((1000 - t) * a.width + t * b.width) / 1000
    dash := match a.dash, b.dash with
      | some (s, l), some (s', l') => some (mixInt s s' t, ((1000 - t) * l + t * l') / 1000)
      | d, _ => d }

/-- A mark retracted to nothing: a dash to no length, a tube to its root. -/
def Mark.gone (m : Mark) : Mark :=
  match m.dash with
  | some (s, _) => { m with dash := some (s, 0) }
  | none => { m with tube := { m.tube with pieces := m.tube.pieces.map fun _ => Piece.zero } }

/-- **Two pictures joined by key**: each mark with its partner, or with itself retracted where it
has none; in the order of the first picture, then the new marks of the second. -/
def join (A B : List Mark) : List (Mark × Mark) :=
  A.map (fun a => (a, (B.find? (·.key == a.key)).getD a.gone)) ++
  (B.filter fun b => !A.any (·.key == b.key)).map fun b => (b.gone, b)

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

/-- The dash pattern and offset of a mark, as text. -/
def dashText (m : Mark) : Option (String × String) :=
  m.dash.map fun (s, l) => (num l ++ " " ++ num BIG, num (-s))

/-- **A mark as a path**, with its animations. -/
def node (m : Mark) (anims : List SvgNode) : SvgNode :=
  .element .path
    ([.attr .d (.path (pathOf m.drawn)), .className ("tube-" ++ m.tone.name), .fill .none,
      .strokeWidth (.fixed 3 m.width), .strokeLinecap (if m.round then .round else .butt),
      .strokeLinejoin .round] ++
     match dashText m with
     | some (a, o) => [.attr .stroke_dasharray a, .attr .stroke_dashoffset o]
     | none => [])
    anims

/-- **An animation** of one attribute through its samples, from `begin` for `dur` milliseconds,
held at its end. -/
def animate (attr : String) (values : List String) (begin_ : String) (dur : Nat) : SvgNode :=
  .element .animate
    [.attr .attributeName attr, .attr .values (";".intercalate values), .attr .begin begin_,
     .attr .dur s!"{dur}ms", .attr .fill "freeze", .attr .calcMode "linear"] []

/-- The animations of one beat of a mark from `a` to `b`: the mix sampled at `K + 1` moments of
the settling ease, and one `animate` for each attribute whose samples differ. -/
def beatAnims (a b : Mark) (K : Nat) (begin_ : String) (dur : Nat) : List SvgNode :=
  if a == b then [] else
  let samples := (List.range (K + 1)).map fun k =>
    a.mix b ((Ease.at .settle (k * 1000 / K)).toNat.min 1000)
  let one (attr : String) (f : Mark → String) : List SvgNode :=
    let vs := samples.map f
    if vs.all (· == vs.headD "") then [] else [animate attr vs begin_ dur]
  one "d" (fun m => pathText m.drawn) ++
  one "stroke-width" (fun m => num m.width) ++
  one "stroke-dasharray" (fun m => ((dashText m).map (·.1)).getD "none") ++
  one "stroke-dashoffset" (fun m => ((dashText m).map (·.2)).getD "0")

/-- The marks in the order of their layers, and in their own order within a layer. -/
def layered (ms : List Mark) : List Mark :=
  (List.range 5).flatMap fun l => ms.filter (·.layer == l)

/-- **A still picture** of `W` by `H` pixels. -/
def still (W H : Nat) (ms : List Mark) : SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view"]
    ((layered ms).map (node · []))

/-- **A film**: pictures played one beat each, every transition the morph of its two pictures. It
starts `delay` milliseconds after the page loads, and again from a click on it; it holds its end.
`id` names the picture, and must be unique on the page. -/
def film (id : String) (W H : Nat) (frames : List (List Mark)) (beat : Nat := 900) (K : Nat := 8)
    (delay : Nat := 500) : SvgNode :=
  match frames with
  | [] => still W H []
  | first :: _ =>
    let steps := frames.zip (frames.drop 1)
    -- every key of the film, with its mark in each picture (retracted where it is absent)
    let keys := (frames.flatMap (·.map (·.key))).eraseDups
    let at_ (ms : List Mark) (k : String) (near : Mark) : Mark := (ms.find? (·.key == k)).getD near.gone
    let marks := keys.filterMap fun k =>
      ((frames.flatMap (·)).find? (·.key == k)).map fun seen =>
        let firstMark := at_ first k seen
        let (anims, _) := (steps.zipIdx).foldl (fun (acc : List SvgNode × Mark) ((A, B), i) =>
          let a := at_ A k acc.2
          let b := at_ B k a
          let begin_ := s!"{delay + i * beat}ms;{id}.click+{i * beat}ms"
          (acc.1 ++ beatAnims a b K begin_ beat, b)) ([], firstMark)
        (firstMark, anims)
    Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view", .ident id]
      ((List.range 5).flatMap fun l =>
        (marks.filter (·.1.layer == l)).map fun (m, anims) => node m anims)

/-- The page's rules for the pen's tones, from the look's ink and ground. -/
def css : String :=
  ".tube-wall { stroke: color-mix(in srgb, var(--e4-color-ink) 30%, var(--e4-color-ground)); }\n" ++
  ".tube-lumen { stroke: color-mix(in srgb, var(--e4-color-ink) 7%, var(--e4-color-ground)); }\n" ++
  ".tube-fluid { stroke: var(--e4-color-ink); }\n" ++
  "svg.tube-view { width: 100%; height: auto; display: block; }\n" ++
  "svg.tube-view[id] { cursor: pointer; }\n"

-- the unit's lengths: a pipe of 8 px holds a unit 24 px long, a vessel of 16 px one 12 px long
#guard unitLen 8000 == 24000 && unitLen 16000 == 12000 && unitLen 48000 == 4000

end Tools.View.Tube
