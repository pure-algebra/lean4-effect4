import Tools.View.Look

/-!
# The outputs of a picture, in a look

Two outputs read a list of device calls (`Tools.View.Picture`) in a look (`Tools.View.Look`):
the stream that `tools/view/draw.c` and `play.c` replay, and SVG. Neither decides a place: each
writes the boxes and texts it is given, in the look's colours and faces.

- **The stream** opens with its target, then the look: one row for each role's colour and one
  for each face. So the painter takes every colour and face from the look, and `paint.h` holds
  none of its own.
- **SVG** names its look on its root (`data-look`), and each element's role and face by a class:
  `e4-fill-<role>`, `e4-stroke-<role>`, `e4-text` and `e4-face-<face>`. The look's values stand as
  presentation attributes, so the file shows as it is. A web page restyles it with a look's CSS
  (`Tools.View.Tokens`), since a class rule overrides a presentation attribute.
-/

namespace Tools.View

/-! ## The stream that `draw.c` replays -/

/-- A text with no tab or line break, so one row holds it. -/
def oneLine (s : String) : String := (s.replace "\t" " ").replace "\n" " "

/-- One row of the stream. A key ends each row that draws, after the fields `draw.c` reads. -/
def Dev.row (key : Key) : Dev → String
  | .fill role value r =>
    s!"F\t{role.code}\t{value}\t{r.x0}\t{r.y0}\t{r.x1}\t{r.y1}\t{oneLine key}"
  | .curve role c w =>
    s!"B\t{role.code}\t{w}\t{c.p0.1}\t{c.p0.2}\t{c.p1.1}\t{c.p1.2}\t{c.p2.1}\t{c.p2.2}\t{c.p3.1}\t{c.p3.2}\t{oneLine key}"
  | .cells x base room s => s!"C\t{x * 1000}\t{base * 1000}\t{room}\t1000\t{oneLine s}\t{oneLine key}"
  | .text face x base room s =>
    s!"T\t{face.code}\t{x * 1000}\t{base * 1000}\t{room * 1000}\t1000\t{oneLine s}\t{oneLine key}"
  | .cut x y w h => s!"K\t{x * 1000}\t{y * 1000}\t{w * 1000}\t{h * 1000}"
  | .uncut => "k"
  | .hit r => s!"H\t{oneLine key}\t{r.x0}\t{r.y0}\t{r.x1}\t{r.y1}"

/-- The look's rows of a stream: each role's colour as `R role rrggbb`, and each face as
`Y face size weight italic families`, its size in thousandths of a logical pixel. The painter
resolves a role of an agent to the ink when the hue is off (`paint__source`, P9), as
`Look.color` does. -/
def lookRows (L : Look) : List String :=
  Role.all.map (fun role => s!"R\t{role.code}\t{(L.palette.of role).hex6}") ++
    Face.all.map fun face =>
      let f := L.faces.of face
      s!"Y\t{face.code}\t{f.size}\t{f.weight}\t{if f.italic then 1 else 0}\t{oneLine (", ".intercalate f.family)}"

/-- The stream of a picture of `W` by `H` logical pixels at the ratio `r`, in a look: the target
(its size and ratio in thousandths, whether the look is light, whether the hue is on, and the
milliseconds of one step of motion), the look's rows, then one row for each device call. -/
def stream (L : Look) (W H r : Nat) (ds : List (Keyed Dev)) : List String :=
  s!"P\t{W * 1000}\t{H * 1000}\t{r * 1000}\t{if L.scheme = .light then 1 else 0}\t{if L.hue then 1 else 0}\t{L.motion.step}" ::
    lookRows L ++ ds.map fun d => d.call.row d.key

/-! ## SVG: the same device calls in a web standard -/

/-- XML's five escapes. -/
def escape (s : String) : String :=
  ((((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;").replace
    "'" "&apos;"

/-- A tone's value as an opacity. -/
def opacity (value : Nat) : String := if value ≥ 1000 then "1" else decimal value 3

/-- The attribute that names a call's object, when it has one. -/
def keyAttr (key : Key) : String := if key.isEmpty then "" else s!" data-key=\"{escape key}\""

/-- A text's attributes in a face of the look: its classes, then the face's family, style,
weight and size, and the ink. -/
def textAttrs (L : Look) (face : Face) : String :=
  let f := L.faces.of face
  s!"class=\"e4-text e4-face-{face.tokenName}\" font-family=\"{escape f.cssFamily}\" font-style=\"{f.style}\" font-weight=\"{f.weight}\" font-size=\"{f.px}\" fill=\"{(L.color .ink).css}\""

/-- One device call as SVG, in device pixels at the ratio `r`, in a look. A cut opens a group
that clips to its box, and its end closes the group. A pointer box is an invisible rectangle
with its key. -/
def Dev.svg (L : Look) (r : Nat) (key : Key) (id : Nat) : Dev → String
  | .fill role value b =>
    s!"<rect class=\"e4-fill-{role.tokenName}\" x=\"{b.x0}\" y=\"{b.y0}\" width=\"{b.x1 - b.x0}\" height=\"{b.y1 - b.y0}\" fill=\"{(L.color role).css}\" fill-opacity=\"{opacity value}\"{keyAttr key}/>"
  | .curve role c w =>
    s!"<path class=\"e4-stroke-{role.tokenName}\" d=\"M {c.p0.1} {c.p0.2} C {c.p1.1} {c.p1.2}, {c.p2.1} {c.p2.2}, {c.p3.1} {c.p3.2}\" fill=\"none\" stroke=\"{(L.color role).css}\" stroke-width=\"{w}\"{keyAttr key}/>"
  | .cells x base room s =>
    let shown := if s.length ≤ room then s else (s.take (room - 1)).toString ++ "…"
    s!"<text x=\"{x}\" y=\"{base}\" {textAttrs L .data} transform=\"scale({r})\" xml:space=\"preserve\"{keyAttr key}>{escape shown}</text>"
  | .text face x base _ s =>
    s!"<text x=\"{x}\" y=\"{base}\" {textAttrs L face} transform=\"scale({r})\" xml:space=\"preserve\"{keyAttr key}>{escape s}</text>"
  | .cut x y w h =>
    s!"<clipPath id=\"c{id}\"><rect x=\"{r * x}\" y=\"{r * y}\" width=\"{r * w}\" height=\"{r * h}\"/></clipPath><g clip-path=\"url(#c{id})\">"
  | .uncut => "</g>"
  | .hit b =>
    s!"<rect x=\"{b.x0}\" y=\"{b.y0}\" width=\"{b.x1 - b.x0}\" height=\"{b.y1 - b.y0}\" fill=\"none\" pointer-events=\"all\"{keyAttr key}/>"

/-- A picture of `W` by `H` logical pixels at the ratio `r`, in a look, as one SVG document. -/
def svg (L : Look) (W H r : Nat) (ds : List (Keyed Dev)) : String :=
  let body := ds.zipIdx.map fun (d, i) => d.call.svg L r d.key i
  "\n".intercalate
    ([s!"<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"e4-view\" data-look=\"{escape L.name}\" width=\"{W}\" height=\"{H}\" viewBox=\"0 0 {r * W} {r * H}\">"] ++
      body ++ ["</svg>"])

end Tools.View
