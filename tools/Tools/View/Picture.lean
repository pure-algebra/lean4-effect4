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

/-- A cubic Bézier segment: its start, its two controls, and its end. A straight segment has its
controls on it. -/
structure Cubic where
  p0 : Int × Int
  p1 : Int × Int
  p2 : Int × Int
  p3 : Int × Int
deriving DecidableEq, Repr

/-- A segment moved by whole pixels. -/
def Cubic.move (dx dy : Int) (c : Cubic) : Cubic :=
  ⟨(c.p0.1 + dx, c.p0.2 + dy), (c.p1.1 + dx, c.p1.2 + dy), (c.p2.1 + dx, c.p2.2 + dy),
    (c.p3.1 + dx, c.p3.2 + dy)⟩

/-- A segment at the ratio `r`: each point in device pixels. -/
def Cubic.scale (r : Int) (c : Cubic) : Cubic :=
  ⟨(r * c.p0.1, r * c.p0.2), (r * c.p1.1, r * c.p1.2), (r * c.p2.1, r * c.p2.2), (r * c.p3.1, r * c.p3.2)⟩

/-- A moved segment, scaled, is the scaled segment moved by `r` times as many pixels. -/
theorem Cubic.scale_move (r dx dy : Int) (c : Cubic) :
    (c.move dx dy).scale r = (c.scale r).move (r * dx) (r * dy) := by
  simp only [Cubic.move, Cubic.scale, Int.mul_add]

/-- The distance between two points along the grid's axes. -/
def gap (p q : Int × Int) : Int := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

/-- A segment's size for a reveal: the length of its control polygon along the axes. -/
def Cubic.size (c : Cubic) : Int := gap c.p0 c.p1 + gap c.p1 c.p2 + gap c.p2 c.p3

/-- The value `e` per mille of the way from `u` to `v`. -/
def lerp (u v e : Int) : Int := v + (u - v) * (1000 - e) / 1000

/-- At the end, the value is the target. -/
theorem lerp_end (u v : Int) : lerp u v 1000 = v := by
  simp only [lerp, Int.sub_self, Int.mul_zero, Int.zero_ediv, Int.add_zero]

/-- The point `t` per mille of the way from `p` to `q`. -/
def lerpPt (p q : Int × Int) (t : Int) : Int × Int := (lerp p.1 q.1 t, lerp p.2 q.2 t)

/-- The part of a segment from its start to `t` per mille along it (de Casteljau's split). -/
def Cubic.upTo (t : Int) (c : Cubic) : Cubic :=
  let a := lerpPt c.p0 c.p1 t
  let b := lerpPt c.p1 c.p2 t
  let e := lerpPt c.p2 c.p3 t
  let ab := lerpPt a b t
  let be := lerpPt b e t
  ⟨c.p0, a, ab, lerpPt ab be t⟩

/-- One call of the painter, in logical pixels at zoom 1. A tone is a role at a value in
thousandths. A rule is a fill whose height, or width, is its weight (`Call.hrule`). A curve is a
stroke of a weight along a cubic segment: an edge of a graph. -/
inductive Call where
  | fill (role : Role) (value : Nat) (x y w h : Int)
  | frame (role : Role) (x y w h : Int) (weight : Nat)
  | curve (role : Role) (c : Cubic) (weight : Nat)
  | cells (x base : Int) (room : Nat) (text : String)
  | text (face : Face) (x base room : Int) (text : String)
  | cut (x y w h : Int)
  | uncut
  | hit (x y w h : Int)
deriving Repr

/-- One call that reaches the target. A curve's points and weight are in device pixels. -/
inductive Dev where
  | fill (role : Role) (value : Nat) (r : Rect)
  | curve (role : Role) (c : Cubic) (weight : Int)
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

/-- A horizontal rule of `w` logical pixels at `(x, y)`: a fill of the rule's weight. At a whole
ratio the painter's weight (P2, `paint_weight`) and a fill's height snap alike, so a rule is no
call of its own. -/
def Call.hrule (role : Role) (x y w : Int) (weight : Nat) : Call := .fill role 1000 x y w weight

/-- A vertical rule of `h` logical pixels at `(x, y)`. -/
def Call.vrule (role : Role) (x y h : Int) (weight : Nat) : Call := .fill role 1000 x y weight h

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

/-- The device pixels of a length or a weight of `v` logical pixels at the ratio `r`: one at
least, so a fill never vanishes (`paint_fill`, `paint_weight`). -/
def span (r v : Int) : Int := if r * v ≤ 0 then 1 else r * v

/-- The box of a fill at a whole ratio: its origin is a product, and its extent is a `span`. -/
def box (r : Int) (x y w h : Int) : Rect :=
  ⟨r * x, r * y, r * x + span r w, r * y + span r h⟩

/-- The device calls of one call of the painter, at the ratio `r`. -/
def lowerCall (r : Int) : Call → List Dev
  | .fill role value x y w h => devFill role value (box r x y w h)
  | .frame role x y w h wt => devFrame role 1000 (box r x y w h) (span r wt)
  | .curve role c wt => [.curve role (c.scale r) (span r wt)]
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

/-- A span is one device pixel at least. -/
theorem span_pos (r v : Int) : 0 < span r v := by
  simp only [span]
  split <;> omega

/-- A fill never vanishes: the box of a fill holds a pixel, at every ratio. -/
theorem box_holds (r x y w h : Int) :
    (box r x y w h).x0 < (box r x y w h).x1 ∧ (box r x y w h).y0 < (box r x y w h).y1 := by
  simp only [box]
  have := span_pos r w
  have := span_pos r h
  constructor <;> omega

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

/-! ## Motion: a move by whole pixels commutes with the lowering

A frame between two pages moves the calls of each object that both pages draw. The law below
makes such a frame exact: moving a call and then lowering it gives the call's own device calls,
moved. So no snap moves a pixel of an object while the object moves, and the device calls of a
moving object are those of the still one, shifted. -/

/-- A box moved by whole device pixels. -/
def Rect.move (dx dy : Int) (b : Rect) : Rect := ⟨b.x0 + dx, b.y0 + dy, b.x1 + dx, b.y1 + dy⟩

/-- A call moved by whole logical pixels. -/
def Call.move (dx dy : Int) : Call → Call
  | .fill role value x y w h => .fill role value (x + dx) (y + dy) w h
  | .frame role x y w h wt => .frame role (x + dx) (y + dy) w h wt
  | .curve role c wt => .curve role (c.move dx dy) wt
  | .cells x base room s => .cells (x + dx) (base + dy) room s
  | .text face x base room s => .text face (x + dx) (base + dy) room s
  | .cut x y w h => .cut (x + dx) (y + dy) w h
  | .uncut => .uncut
  | .hit x y w h => .hit (x + dx) (y + dy) w h

/-- A device call moved by whole logical pixels at the ratio `r`: a box by `r` times as many
device pixels; a text and a cut, which stay in logical pixels, by the logical move. -/
def Dev.move (r dx dy : Int) : Dev → Dev
  | .fill role value b => .fill role value (b.move (r * dx) (r * dy))
  | .curve role c w => .curve role (c.move (r * dx) (r * dy)) w
  | .cells x base room s => .cells (x + dx) (base + dy) room s
  | .text face x base room s => .text face (x + dx) (base + dy) room s
  | .cut x y w h => .cut (x + dx) (y + dy) w h
  | .uncut => .uncut
  | .hit b => .hit (b.move (r * dx) (r * dy))

/-- A box at a moved origin is the box, moved. -/
theorem box_move (r x y w h dx dy : Int) :
    box r (x + dx) (y + dy) w h = (box r x y w h).move (r * dx) (r * dy) := by
  simp only [box, Rect.move, Int.mul_add, Int.add_right_comm (r * x) (span r w) (r * dx),
    Int.add_right_comm (r * y) (span r h) (r * dy)]

/-- A fill of a moved box is the fill, moved. -/
theorem devFill_move (role : Role) (value : Nat) (b : Rect) (r dx dy : Int) :
    devFill role value (b.move (r * dx) (r * dy)) = (devFill role value b).map (Dev.move r dx dy) := by
  simp only [devFill, Rect.move, Int.add_le_add_iff_right]
  by_cases h : b.x1 ≤ b.x0 ∨ b.y1 ≤ b.y0
  · simp only [h, ↓reduceIte, List.map_nil]
  · simp only [h, ↓reduceIte, List.map_cons, List.map_nil, Dev.move, Rect.move]

/-- The sides of a moved frame are the sides, moved. -/
theorem frameSides_move (b : Rect) (w dx dy : Int) :
    frameSides (b.move dx dy) w = (frameSides b w).map (Rect.move dx dy) := by
  simp only [frameSides, Rect.move, List.map_cons, List.map_nil, Int.sub_eq_add_neg,
    Int.add_right_comm _ dx, Int.add_right_comm _ dy]

/-- A moved frame lowers to the frame's device calls, moved. -/
theorem devFrame_move (role : Role) (value : Nat) (b : Rect) (w r dx dy : Int) :
    devFrame role value (b.move (r * dx) (r * dy)) w =
      (devFrame role value b w).map (Dev.move r dx dy) := by
  simp only [devFrame]
  have hx : (b.move (r * dx) (r * dy)).x1 - (b.move (r * dx) (r * dy)).x0 = b.x1 - b.x0 :=
    Int.add_sub_add_right _ _ _
  have hy : (b.move (r * dx) (r * dy)).y1 - (b.move (r * dx) (r * dy)).y0 = b.y1 - b.y0 :=
    Int.add_sub_add_right _ _ _
  rw [hx, hy]
  by_cases h : b.x1 - b.x0 ≤ 2 * w ∨ b.y1 - b.y0 ≤ 2 * w
  · simp only [h, ↓reduceIte]
    exact devFill_move role value b r dx dy
  · simp only [h, ↓reduceIte, frameSides_move, List.flatMap_map, List.map_flatMap, devFill_move]

/-- **The move law.** A call moved by whole logical pixels lowers to its device calls, moved. -/
theorem lowerCall_move (r dx dy : Int) (c : Call) :
    lowerCall r (c.move dx dy) = (lowerCall r c).map (Dev.move r dx dy) := by
  cases c with
  | fill role value x y w h =>
    simp only [Call.move, lowerCall]
    rw [box_move, devFill_move]
  | frame role x y w h wt =>
    simp only [Call.move, lowerCall]
    rw [box_move, devFrame_move]
  | curve role c wt =>
    simp only [Call.move, lowerCall, List.map_cons, List.map_nil, Dev.move, Cubic.scale_move]
  | cells => rfl
  | text => rfl
  | cut => rfl
  | uncut => rfl
  | hit x y w h =>
    simp only [Call.move, lowerCall, List.map_cons, List.map_nil, Dev.move]
    rw [box_move]

/-- A keyed call moved by whole logical pixels. -/
def Keyed.move (dx dy : Int) (c : Keyed Call) : Keyed Call := ⟨c.key, c.call.move dx dy⟩

/-- A keyed device call moved by whole logical pixels at the ratio `r`. -/
def Keyed.moveDev (r dx dy : Int) (d : Keyed Dev) : Keyed Dev := ⟨d.key, d.call.move r dx dy⟩

/-- **The move law, keyed.** A keyed call moved by whole logical pixels lowers to its device
calls, moved, each with the call's key. -/
theorem lower_move (r dx dy : Int) (c : Keyed Call) :
    lower r (c.move dx dy) = (lower r c).map (Keyed.moveDev r dx dy) := by
  simp only [lower, Keyed.move, lowerCall_move, List.map_map]
  rfl

/-- A list of keyed calls moved alike lowers to its device calls, moved. -/
theorem lowerAll_move (r dx dy : Int) (cs : List (Keyed Call)) :
    lowerAll r (cs.map (Keyed.move dx dy)) = (lowerAll r cs).map (Keyed.moveDev r dx dy) := by
  simp only [lowerAll, List.flatMap_map, List.map_flatMap, lower_move]

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

/-- The stream of a picture of `W` by `H` logical pixels at the ratio `r`: the target, then
one row for each device call. -/
def stream (W H r : Nat) (ds : List (Keyed Dev)) : List String :=
  s!"P\t{W * 1000}\t{H * 1000}\t{r * 1000}\t0\t0" :: ds.map fun d => d.call.row d.key

/-! ## SVG: the same device calls in a web standard -/

/-- The dark tokens of `paint.h` (`PAINT_DARK`), as CSS colours. With the hue off, the role of
an agent (the host, a failure, a resource) is drawn in the ink, as `paint__source` draws it (P9):
the base is black and white. -/
def Role.css (hue : Bool := false) : Role → String
  | .ground => "#14110d" | .ink => "#f3f4f6" | .rule => "#45433f"
  | .host => if hue then "#c0851f" else "#f3f4f6"
  | .failure => if hue then "#bd3931" else "#f3f4f6"
  | .resource => if hue then "#359b75" else "#f3f4f6"

/-- The families of `paint_faces_open`, and each face's size in logical pixels, as text. The data
face's size is the one whose advance is one cell of 8 pixels in Menlo, 13.288 pixels (the forms
note, section 5). -/
def Face.css : Face → String × String × String
  | .data => ("Menlo, DejaVu Sans Mono, monospace", "normal", "13.288")
  | .name => ("Georgia, Charter, serif", "normal", "15")
  | .label => ("Georgia, Charter, serif", "italic", "13.5")
  | .title => ("Georgia, Charter, serif", "normal", "20")

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
    s!"<rect x=\"{b.x0}\" y=\"{b.y0}\" width=\"{b.x1 - b.x0}\" height=\"{b.y1 - b.y0}\" fill=\"{role.css false}\" fill-opacity=\"{opacity value}\"{keyAttr key}/>"
  | .curve role c w =>
    s!"<path d=\"M {c.p0.1} {c.p0.2} C {c.p1.1} {c.p1.2}, {c.p2.1} {c.p2.2}, {c.p3.1} {c.p3.2}\" fill=\"none\" stroke=\"{role.css false}\" stroke-width=\"{w}\"{keyAttr key}/>"
  | .cells x base room s =>
    let (family, style, size) := Face.css .data
    let shown := if s.length ≤ room then s else (s.take (room - 1)).toString ++ "…"
    s!"<text x=\"{x}\" y=\"{base}\" font-family=\"{family}\" font-style=\"{style}\" font-size=\"{size}\" transform=\"scale({r})\" fill=\"{Role.css false .ink}\" xml:space=\"preserve\"{keyAttr key}>{escape shown}</text>"
  | .text face x base _ s =>
    let (family, style, size) := face.css
    s!"<text x=\"{x}\" y=\"{base}\" font-family=\"{family}\" font-style=\"{style}\" font-size=\"{size}\" transform=\"scale({r})\" fill=\"{Role.css false .ink}\" xml:space=\"preserve\"{keyAttr key}>{escape s}</text>"
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
