/-!
# The picture as data: drawing calls, device calls, and their outputs

Slice V0 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`; decisions row 336).
It lands the lowest two forms of the native view probe of 2026-10-07
(`docs/research/2026-10-06-native-view-probe/Scene.lean`), with one change: **every call
carries a key**, the name of the object it draws. A key joins one object's calls across two
frames, and it answers the pointer.

- `Call`: one call of the painter (`tools/view/paint.h`), in logical pixels at zoom 1.
- `Dev`: one call that reaches the target. A fill is a box of whole device pixels in the tone of
  a role. A text is left to the host, with its face, its place and its room.
- `lower`: a call to device calls, at a whole ratio of device pixels to logical pixels.

Two outputs read a list of device calls: the stream that `tools/view/draw.c` replays
(`Dev.row`), and SVG (`svg`). Neither decides a place: each writes the boxes and texts it is
given.

The layout is a tool's, so the laws below are statements of the tool, not registry claims
(decisions row 334, point 3). They are the probe's five, less the two shapes that no page here
draws, plus `lower_key`.
-/

namespace Tools.View

/-- A role of the tokens, in the order of `PaintRole` (`tools/view/paint.h`). -/
inductive Role where
  | ground | ink | rule | host | failure | resource
deriving DecidableEq, Repr

/-- The code `paint.h` reads. -/
def Role.code : Role → Nat
  | .ground => 0 | .ink => 1 | .rule => 2 | .host => 3 | .failure => 4 | .resource => 5

/-- A face of the type, in the order of `PaintFace`: the data face is monospace, one cell for
each character; a name and a title are in the display face; a label is its italic. -/
inductive Face where
  | data | name | label | title
deriving DecidableEq, Repr

/-- The code `paint.h` reads. -/
def Face.code : Face → Nat
  | .data => 0 | .name => 1 | .label => 2 | .title => 3

/-- A key: the name of the object that a call draws, such as the address of a node. The empty
key names no object. -/
abbrev Key := String

/-- A box of whole device pixels: `[x0, x1)` by `[y0, y1)`. -/
structure Rect where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
deriving DecidableEq, Repr

/-- One call of the painter, in logical pixels at zoom 1. A tone is a role at a value in
thousandths. -/
inductive Call where
  | fill (role : Role) (value : Nat) (x y w h : Int)
  | hrule (role : Role) (x0 x1 y : Int) (weight : Nat)
  | vrule (role : Role) (x y0 y1 : Int) (weight : Nat)
  | frame (role : Role) (x y w h : Int) (weight : Nat)
  | cells (x base : Int) (room : Nat) (text : String)
  | text (face : Face) (x base room : Int) (text : String)
  | cut (x y w h : Int)
  | uncut
  | hit (x y w h : Int)
deriving Repr

/-- One call that reaches the target. -/
inductive Dev where
  | fill (role : Role) (value : Nat) (r : Rect)
  | cells (x base : Int) (room : Nat) (text : String)
  | text (face : Face) (x base room : Int) (text : String)
  | cut (x y w h : Int)
  | uncut
  | hit (r : Rect)
deriving Repr

/-- A call with the key of the object it draws. -/
structure Keyed (α : Type) where
  key : Key
  call : α
deriving Repr

/-! ## From a call to device calls: the painter's snapping, at a whole ratio -/

/-- A fill; an empty box paints nothing (`paint_device_fill`). -/
def devFill (role : Role) (value : Nat) (r : Rect) : List Dev :=
  if r.x1 ≤ r.x0 ∨ r.y1 ≤ r.y0 then [] else [.fill role value r]

/-- The four sides of a frame, `w` thick inside the box: top, bottom, left, right. -/
def frameSides (b : Rect) (w : Int) : List Rect :=
  [ ⟨b.x0, b.y0, b.x1, b.y0 + w⟩, ⟨b.x0, b.y1 - w, b.x1, b.y1⟩
  , ⟨b.x0, b.y0 + w, b.x0 + w, b.y1 - w⟩, ⟨b.x1 - w, b.y0 + w, b.x1, b.y1 - w⟩ ]

/-- A frame; a box too small for a hole is filled (`paint_device_frame`). -/
def devFrame (role : Role) (value : Nat) (b : Rect) (w : Int) : List Dev :=
  if b.x1 - b.x0 ≤ 2 * w ∨ b.y1 - b.y0 ≤ 2 * w then devFill role value b
  else (frameSides b w).flatMap (devFill role value)

/-- The box of a fill: each edge is snapped by itself, and a fill keeps one pixel
(`paint_fill`). At a whole ratio the snap is a product. -/
def box (r : Int) (x y w h : Int) : Rect :=
  let x0 := r * x
  let y0 := r * y
  ⟨x0, y0, if r * (x + w) ≤ x0 then x0 + 1 else r * (x + w),
    if r * (y + h) ≤ y0 then y0 + 1 else r * (y + h)⟩

/-- The device pixels of a weight: one at least (`paint_weight`). -/
def weight (r : Int) (w : Nat) : Int := if r * w < 1 then 1 else r * w

/-- The device calls of one call of the painter, at the ratio `r`. -/
def lowerCall (r : Int) : Call → List Dev
  | .fill role value x y w h => devFill role value (box r x y w h)
  | .hrule role x0 x1 y w =>
    let a := r * min x0 x1
    let b := if r * max x0 x1 ≤ a then a + 1 else r * max x0 x1
    devFill role 1000 ⟨a, r * y, b, r * y + weight r w⟩
  | .vrule role x y0 y1 w =>
    let a := r * min y0 y1
    let b := if r * max y0 y1 ≤ a then a + 1 else r * max y0 y1
    devFill role 1000 ⟨r * x, a, r * x + weight r w, b⟩
  | .frame role x y w h wt => devFrame role 1000 (box r x y w h) (weight r wt)
  | .cells x base room text => [.cells x base room text]
  | .text face x base room text => [.text face x base room text]
  | .cut x y w h => [.cut x y w h]
  | .uncut => [.uncut]
  | .hit x y w h => [.hit (box r x y w h)]

/-- A keyed call's device calls, each with the call's key. -/
def lower (r : Int) (c : Keyed Call) : List (Keyed Dev) :=
  (lowerCall r c.call).map fun d => ⟨c.key, d⟩

/-- A list of calls, lowered call by call. -/
def lowerAll (r : Int) (cs : List (Keyed Call)) : List (Keyed Dev) := cs.flatMap (lower r)

/-! ## The pointer, and the laws of the lowering -/

/-- Two boxes share no pixel. -/
def Rect.Disjoint (a b : Rect) : Prop := a.x1 ≤ b.x0 ∨ b.x1 ≤ a.x0 ∨ a.y1 ≤ b.y0 ∨ b.y1 ≤ a.y0

/-- A box holds a pixel. -/
def Rect.holds (r : Rect) (x y : Int) : Bool := r.x0 ≤ x && x < r.x1 && r.y0 ≤ y && y < r.y1

/-- The key that one device call answers at a pixel: a pointer box answers its key. -/
def keyAt (x y : Int) (d : Keyed Dev) : Option Key :=
  match d.call with
  | .hit r => if r.holds x y then some d.key else none
  | _ => none

/-- The key under a pixel: the last pointer box that holds it answers. -/
def pick (ds : List (Keyed Dev)) (x y : Int) : Option Key := ds.reverse.findSome? (keyAt x y)

/-- The lowering is a map of lists: a page lowers call by call. -/
theorem lowerAll_append (r : Int) (a b : List (Keyed Call)) :
    lowerAll r (a ++ b) = lowerAll r a ++ lowerAll r b := by
  simp only [lowerAll, List.flatMap_append]

/-- Every device call carries the key of the call it lowers. So the pixels of one object are
found by its key in every frame, and a pointer box answers the object its call drew. -/
theorem lower_key (r : Int) (c : Keyed Call) (d : Keyed Dev) (h : d ∈ lower r c) :
    d.key = c.key := by
  simp only [lower, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- A later call answers the pointer before an earlier one. -/
theorem pick_append (a b : List (Keyed Dev)) (x y : Int) :
    pick (a ++ b) x y = (pick b x y).or (pick a x y) := by
  simp only [pick, List.reverse_append, List.findSome?_append]

/-- A fill never vanishes: the box of a fill holds a pixel, at a ratio of one or more. -/
theorem box_holds (r x y w h : Int) (_hr : 0 < r) :
    (box r x y w h).x0 < (box r x y w h).x1 ∧ (box r x y w h).y0 < (box r x y w h).y1 := by
  simp only [box]
  constructor <;> split <;> omega

/-- The four sides of a frame share no pixel (the painter's P4). -/
theorem frameSides_pairwise (b : Rect) (w : Int)
    (hx : 2 * w < b.x1 - b.x0) (hy : 2 * w < b.y1 - b.y0) :
    (frameSides b w).Pairwise Rect.Disjoint := by
  unfold frameSides
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by show b.y0 + w ≤ b.y1 - w; omega)))
    · exact Or.inr (Or.inr (Or.inl (Int.le_refl _)))
    · exact Or.inr (Or.inr (Or.inl (Int.le_refl _)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Int.le_refl _)))
    · exact Or.inr (Or.inr (Or.inr (Int.le_refl _)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact Or.inl (by show b.x0 + w ≤ b.x1 - w; omega)
  · intro r hr
    cases hr

/-! ## The stream that `draw.c` replays -/

/-- A text with no tab or line break, so one row holds it. -/
def oneLine (s : String) : String := (s.replace "\t" " ").replace "\n" " "

/-- One row of the stream. A key ends each row that draws, after the fields `draw.c` reads. -/
def Dev.row (key : Key) : Dev → String
  | .fill role value r =>
    s!"F\t{role.code}\t{value}\t{r.x0}\t{r.y0}\t{r.x1}\t{r.y1}\t{oneLine key}"
  | .cells x base room s => s!"C\t{x * 1000}\t{base * 1000}\t{room}\t1000\t{oneLine s}\t{oneLine key}"
  | .text face x base room s =>
    s!"T\t{face.code}\t{x * 1000}\t{base * 1000}\t{room * 1000}\t1000\t{oneLine s}\t{oneLine key}"
  | .cut x y w h => s!"K\t{x * 1000}\t{y * 1000}\t{w * 1000}\t{h * 1000}"
  | .uncut => "k"
  | .hit r => s!"H\t{oneLine key}\t{r.x0}\t{r.y0}\t{r.x1}\t{r.y1}"

/-- The stream of a picture of `W` by `H` logical pixels at the ratio `r`: the target, then
one row for each device call. -/
def stream (W H r : Nat) (ds : List (Keyed Dev)) : List String :=
  s!"P\t{W * 1000}\t{H * 1000}\t{r * 1000}\t0\t0" :: ds.map fun d => d.call.row d.key

/-! ## SVG: the same device calls in a web standard -/

/-- The dark tokens of `paint.h` (`PAINT_DARK`), as CSS colours. -/
def Role.css : Role → String
  | .ground => "#14110d" | .ink => "#f3f4f6" | .rule => "#45433f"
  | .host => "#c0851f" | .failure => "#bd3931" | .resource => "#359b75"

/-- The families of `paint_faces_open`, and each face's size in logical pixels. The data face's
size is the one whose advance is one cell of 8 pixels in Menlo. -/
def Face.css : Face → String × String × Nat
  | .data => ("Menlo, DejaVu Sans Mono, monospace", "normal", 13)
  | .name => ("Georgia, Charter, serif", "normal", 15)
  | .label => ("Georgia, Charter, serif", "italic", 13)
  | .title => ("Georgia, Charter, serif", "normal", 20)

/-- XML's five escapes. -/
def escape (s : String) : String :=
  ((((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;").replace "\"" "&quot;").replace
    "'" "&apos;"

/-- A tone's value as an opacity. -/
def opacity (value : Nat) : String :=
  if value ≥ 1000 then "1" else s!"0.{(toString (value + 1000)).drop 1}"

/-- The attribute that names a call's object, when it has one. -/
def keyAttr (key : Key) : String := if key.isEmpty then "" else s!" data-key=\"{escape key}\""

/-- One device call as SVG, in device pixels at the ratio `r`. A cut opens a group that clips to
its box, and its end closes the group. A pointer box is an invisible rectangle with its key. -/
def Dev.svg (r : Nat) (key : Key) (id : Nat) : Dev → String
  | .fill role value b =>
    s!"<rect x=\"{b.x0}\" y=\"{b.y0}\" width=\"{b.x1 - b.x0}\" height=\"{b.y1 - b.y0}\" fill=\"{role.css}\" fill-opacity=\"{opacity value}\"{keyAttr key}/>"
  | .cells x base room s =>
    let (family, style, size) := Face.css .data
    let shown := if s.length ≤ room then s else (s.take (room - 1)).toString ++ "…"
    s!"<text x=\"{r * x}\" y=\"{r * base}\" font-family=\"{family}\" font-style=\"{style}\" font-size=\"{r * size}\" fill=\"{Role.css .ink}\" xml:space=\"preserve\"{keyAttr key}>{escape shown}</text>"
  | .text face x base _ s =>
    let (family, style, size) := face.css
    s!"<text x=\"{r * x}\" y=\"{r * base}\" font-family=\"{family}\" font-style=\"{style}\" font-size=\"{r * size}\" fill=\"{Role.css .ink}\" xml:space=\"preserve\"{keyAttr key}>{escape s}</text>"
  | .cut x y w h =>
    s!"<clipPath id=\"c{id}\"><rect x=\"{r * x}\" y=\"{r * y}\" width=\"{r * w}\" height=\"{r * h}\"/></clipPath><g clip-path=\"url(#c{id})\">"
  | .uncut => "</g>"
  | .hit b =>
    s!"<rect x=\"{b.x0}\" y=\"{b.y0}\" width=\"{b.x1 - b.x0}\" height=\"{b.y1 - b.y0}\" fill=\"none\" pointer-events=\"all\"{keyAttr key}/>"

/-- A picture of `W` by `H` logical pixels at the ratio `r`, as one SVG document. -/
def svg (W H r : Nat) (ds : List (Keyed Dev)) : String :=
  let body := ds.zipIdx.map fun (d, i) => d.call.svg r d.key i
  "\n".intercalate
    ([s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{W}\" height=\"{H}\" viewBox=\"0 0 {r * W} {r * H}\">"] ++
      body ++ ["</svg>"])

end Tools.View
