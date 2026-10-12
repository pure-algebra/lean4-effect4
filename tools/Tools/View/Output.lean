import Tools.View.Look

/-!
# The outputs of a picture, in a look

Two outputs read a list of device calls (`Tools.View.Picture`) in a look (`Tools.View.Look`):
the stream that `tools/view/draw.c` and `play.c` replay, here, and SVG, a typed tree on the kit
of `lean4-whatwg` (`Tools.View.SvgOut`). Neither decides a place: each writes the boxes and texts
it is given, in the look's colours and faces.

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

/-- A closed path's points in a row: its start, then each segment's two controls and its end, in
thousandths of a device pixel, separated by spaces. -/
def pathRow (p : List Cubic) : String :=
  match p with
  | [] => ""
  | c :: _ => " ".intercalate ([toString c.p0.1, toString c.p0.2] ++
      p.flatMap fun c => [c.p1.1, c.p1.2, c.p2.1, c.p2.2, c.p3.1, c.p3.2].map toString)

/-- A closed path as SVG's path data, in device pixels: `M`, a `C` for each segment, `Z`. -/
def pathData (p : List Cubic) : String :=
  let d (v : Int) : String := decimal v 3
  match p with
  | [] => ""
  | c :: _ => s!"M {d c.p0.1} {d c.p0.2} " ++ " ".intercalate (p.map fun c =>
      s!"C {d c.p1.1} {d c.p1.2}, {d c.p2.1} {d c.p2.2}, {d c.p3.1} {d c.p3.2}") ++ " Z"

/-- One row of the stream. A key ends each row that draws, after the fields `draw.c` reads. A
shape's row holds one field for each of its closed paths. -/
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
  | .shape role value ps =>
    s!"S\t{role.code}\t{value}\t" ++ "\t".intercalate (ps.map pathRow) ++ s!"\t{oneLine key}"

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

/-! ## Text for a page -/

/-- XML's five escapes, for the view's pages that are written as text. -/
def escape (s : String) : String :=
  ((((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;").replace
    "'" "&apos;"

end Tools.View
