import Tools.View.Look
import Whatwg.Html.Node.SvgBuild
import Whatwg.Html.Node.SvgPaint
import Whatwg.Html.Node.SvgNest
import Whatwg.Html.Print.Picture
import Whatwg.Html.Content.Explain
import Whatwg.Svg.Geometry.Pen
import Whatwg.Svg.Geometry.Arith

/-!
# A picture as a typed SVG tree

The SVG output of a list of device calls (`Tools.View.Picture`) in a look, written on the SVG kit
of `lean4-whatwg` (decisions rows 358 and 360). It is the kit's own port of this package's string
writer (`WhatwgTest/Html/SvgKit.lean` at the pin) on this package's types. Each device call is one
typed node. A cut and its end become a clip group (`SvgNode.nest`), so a list with a stray end or
an open cut still gives a balanced tree. The picture is `Svg.Frame.svg`.

What the kit's laws give: every value of a typed tree passes its grammar
(`SvgNode.valuesOk_toRaw`). The structure is checked at run time, where a file is written
(`fileText`): the located refusal of the content model where a figure stands, then XML's
characters and names. No structure theorem enters Effect4 (row 358).

The text differs from the string writer it replaces: one line for the picture; the geometry first
on `rect` and `path`; path data in the grammar's spelling (`M10,20C10,30 30,30 30,40`); `'` and `>`
as they are; a negative size written as zero. The stream (`Tools.View.Output`) is unchanged.
-/

namespace Tools.View.SvgOut

open Whatwg.Html hiding Rgb
open Whatwg.Svg.Value (Decimal Pen Point)

/-! ## One node for each device call -/

/-- A point in thousandths of a device pixel. -/
def milli (p : Int × Int) : Point := .fixed 3 p.1 p.2

/-- A tone's value as an opacity: thousandths, and one from a thousand up. -/
def opacity (value : Nat) : Decimal := .fixed 3 (min value 1000)

/-- A role's colour in the look (`Look.color`), as the kit's colour. -/
def paint (L : Look) (role : Role) : Whatwg.Html.Rgb := .ofNat (L.color role)

/-- A filled box. A negative size is written as zero. -/
def fillNode (L : Look) (role : Role) (value : Nat) (b : Rect) (key : Key) : SvgNode :=
  Svg.rect b.x0 b.y0 (.clamp (b.x1 - b.x0)) (.clamp (b.y1 - b.y0))
    ([.className ("e4-fill-" ++ role.tokenName), .fill (paint L role),
      .fillOpacity (opacity value)] ++ SvgAttr.dataKey? key)

/-- A stroked cubic curve, in whole device pixels. -/
def curveNode (L : Look) (role : Role) (c : Cubic) (weight : Int) (key : Key) : SvgNode :=
  Svg.path (Pen.begin (.ofPair c.p0) |>.curveTo (.ofPair c.p1) (.ofPair c.p2) (.ofPair c.p3)).path
    ([.className ("e4-stroke-" ++ role.tokenName), .fill .none, .stroke (paint L role),
      .strokeWidth weight] ++ SvgAttr.dataKey? key)

/-- A text in a face of the look, scaled by the ratio. -/
def textNode (L : Look) (ratio : Nat) (face : Face) (x base : Int) (content : String) (key : Key) :
    SvgNode :=
  let f := L.faces.of face
  Svg.text x base content
    ([.className ("e4-text e4-face-" ++ face.tokenName), .fontFamily f.cssFamily,
      .fontStyle f.italic, .fontWeight f.weight, .fontSize (.fixed 3 f.size),
      .fill (paint L .ink), .attr .transform [.scale (.ofInt ratio) none], .xmlSpacePreserve] ++
      SvgAttr.dataKey? key)

/-- The text of `cells` in its room: a longer one is cut, and ends in an ellipsis. -/
def shown (room : Nat) (s : String) : String :=
  if s.length ≤ room then s else (s.take (room - 1)).toString ++ "…"

/-- An invisible box that takes the pointer. -/
def hitNode (b : Rect) (key : Key) : SvgNode :=
  Svg.rect b.x0 b.y0 (.clamp (b.x1 - b.x0)) (.clamp (b.y1 - b.y0))
    ([.fill .none, .pointerEvents "all"] ++ SvgAttr.dataKey? key)

/-- One closed path as a pen: its start, a curve for each segment, and a closepath. A path with
no segment is no pen. -/
def closedPen : List Cubic → Option Pen
  | [] => none
  | c :: rest =>
    some ((c :: rest).foldl (fun pen s => pen.curveTo (milli s.p1) (milli s.p2) (milli s.p3))
      (Pen.begin (milli c.p0))).close

/-- A filled shape of several closed paths in one `d`, in thousandths of a device pixel. -/
def shapeNode (L : Look) (role : Role) (value : Nat) (paths : List (List Cubic)) (key : Key) :
    SvgNode :=
  Svg.path (Pen.join (paths.filterMap closedPen))
    ([.className ("e4-fill-" ++ role.tokenName), .fillRule true, .fill (paint L role),
      .fillOpacity (opacity value)] ++ SvgAttr.dataKey? key)

/-- An open cut: the index of its call, and its box in logical pixels. -/
structure Cut where
  id : Nat
  x : Int
  y : Int
  w : Int
  h : Int

/-- A cut around the marks drawn inside it: a clip path of its box in device pixels, and the
group it clips. -/
def cutNodes (ratio : Nat) (c : Cut) (children : List SvgNode) : List SvgNode :=
  Svg.clipped ("c" ++ toString c.id)
    [Svg.rect (ratio * c.x : Int) (ratio * c.y : Int) (.clamp (ratio * c.w))
      (.clamp (ratio * c.h))] children

/-! ## The fold and the picture -/

/-- One device call with its index in the list: a mark, the start of a cut under that index, or
the end of the innermost cut. -/
def flat (L : Look) (ratio : Nat) (d : Keyed Dev × Nat) : SvgNode.Flat Cut :=
  match d.1.call with
  | .fill role value b => .leaf (fillNode L role value b d.1.key)
  | .curve role c weight => .leaf (curveNode L role c weight d.1.key)
  | .cells x base room s => .leaf (textNode L ratio .data x base (shown room s) d.1.key)
  | .text face x base _ s => .leaf (textNode L ratio face x base s d.1.key)
  | .cut x y w h => .enter ⟨d.2, x, y, w, h⟩
  | .uncut => .leave
  | .hit b => .leaf (hitNode b d.1.key)
  | .shape role value paths => .leaf (shapeNode L role value paths d.1.key)

/-- The marks of a list of device calls, in order. An end with no open cut is dropped, and a cut
with no end is closed at the end of the list. -/
def marksOf (L : Look) (ratio : Nat) (calls : List (Keyed Dev)) : List SvgNode :=
  SvgNode.nest (cutNodes ratio) (calls.zipIdx.map (flat L ratio))

/-- The picture of `W` by `H` logical pixels at a ratio, in a look. -/
def picture (L : Look) (W H ratio : Nat) (calls : List (Keyed Dev)) : SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := ratio }
    [.className "e4-view", .data "look" L.name] (marksOf L ratio calls)

/-! ## A picture whose marks link -/

/-- A group of a linked picture: a cut, or a link to `href`. -/
abbrev Group := Sum Cut String

/-- The marks of a list of device calls, each run of marks of one linked key inside one SVG `a`
(the figure's nodes, `Tools.Document.Figure`). A cut's start or end closes an open link first, so
a link never crosses a clip group. -/
def linkedMarks (L : Look) (ratio : Nat) (link : Key → Option String) (calls : List (Keyed Dev)) :
    List SvgNode := Id.run do
  let mut out : Array (SvgNode.Flat Group) := #[]
  let mut opened : Option Key := none
  for (d, i) in calls.zipIdx do
    let f := flat L ratio (d, i)
    let want := match f with
      | .leaf _ => (link d.key).map fun href => (d.key, href)
      | _ => none
    if opened.isSome && opened != want.map (·.1) then
      out := out.push .leave
      opened := none
    if opened.isNone then
      if let some (k, href) := want then
        out := out.push (.enter (.inr href))
        opened := some k
    out := out.push (match f with
      | .leaf n => .leaf n
      | .enter c => .enter (.inl c)
      | .leave => .leave)
  if opened.isSome then out := out.push .leave
  return SvgNode.nest (fun
    | .inl c => cutNodes ratio c
    | .inr href => fun children => [.element .a [.attr .href href] children]) out.toList

/-- **A picture whose nodes link**: `picture`, with each run of marks of a key that `link` answers
inside a link to it. -/
def linkedPicture (L : Look) (W H ratio : Nat) (link : Key → Option String) (calls : List (Keyed Dev)) :
    SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := ratio }
    [.className "e4-view", .data "look" L.name] (linkedMarks L ratio link calls)

/-- The text of a picture as a file, or why it is refused: the content model where a figure
stands (flow content), by its located refusal, then XML's characters and names. -/
def fileText (pic : SvgNode) : Except String String := do
  if let some r := Whatwg.Html.Content.explain Whatwg.Html.Content.Ctx.flow pic.toRaw then
    throw s!"refused at the child path {r.path}: {r.reason.describe}"
  match pic.renderXml? with
  | some text => return text
  | none => throw "no XML: a control character in a text, or a data key that is no XML name"

end Tools.View.SvgOut
