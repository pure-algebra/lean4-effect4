import Tools.View.Graph

/-!
# A page of lines, and its calls

Slice V0 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`). A page is the
form a frame takes before it is drawn: a title block, then lines, then a foot. A line is one node
of a tree: its address in the gutter, its text indented by its depth, its type, and a note.

The layout transcribes the native view probe's painter for a line of a program
(`docs/research/2026-10-06-native-view-probe/Scene.lean`, `lineOps` and `pageOps`) on the grid of
`tools/view/paint.h`: a cell is 8 logical pixels, a row 24, and a baseline 16 below the row's
top. It draws no mark: the probe's marks wait for the owner's ruling (its proposal A).

Each line's calls carry the line's key, so a line keeps its identity from frame to frame.
-/

namespace Tools.View

/-- The state of a line that the page shows: plain; lit, as the subject of the step; or refused,
framed in the failure tone. -/
inductive LineState where
  | plain | lit | refused
deriving DecidableEq, Repr

/-! ## Marks

A mark tells how an operation is answered, in the design language's parts: a hollow square is a
promise, a filled square a promise kept, dots the wait between them, and a bar a decision of the
host (`docs/research/2026-10-07-native-view-forms.md`, section 5). Each shape is a box of whole
logical pixels on the grid, so a mark is plain fills and frames: it needs no call of its own, and
it moves as the move law moves every call (`lowerCall_move`). Marks wait for the owner's ruling
(the forms note's proposal A, 1), so a page draws them only when `marks` is set. -/

/-- One shape of a part, in logical pixels from the part's left edge and the line's baseline: a
filled square, a ring, a dotted rule, a bar of a role reaching above and below, a rule over the
row's top, a rule under its baseline. -/
inductive Shape where
  | square (x0 : Int)
  | ring (x0 : Int)
  | dots (x0 x1 pitch : Int)
  | post (x0 x1 reach : Int) (role : Role)
  | over (x0 x1 : Int)
  | under (x0 x1 : Int)
deriving Repr

/-- A part of a mark: the cells it takes, its shapes, and its glyph in a terminal. -/
structure Part where
  cells : Nat
  shapes : List Shape
  glyph : String
deriving Repr

/-- A promise: a hollow square. -/
def Part.hollow : Part := ⟨1, [.ring 0], "□"⟩
/-- The wait: a dotted rule over two cells. -/
def Part.dotted : Part := ⟨2, [.dots 1 14 3], "┄┄"⟩
/-- A decision of the host: a bar in the host's role. -/
def Part.bar : Part := ⟨1, [.post 2 4 4 .host], "┃"⟩
/-- A promise kept: a filled square. -/
def Part.filled : Part := ⟨1, [.square 0], "■"⟩

/-- A mark: its parts, side by side. -/
abbrev Mark := List Part

/-- The fills of a dotted rule from `a` to `b` at `top`: dots of one pixel at a pitch, centred
(`paint_device_dots` at zoom 1). -/
def dotCalls (key : Key) (a b top pitch : Int) : List (Keyed Call) :=
  if b - a < 1 then [⟨key, .fill .ink 1000 a top (b - a) 1⟩]
  else
    let pitch := if pitch ≤ 1 then 2 else pitch
    let n := (b - a - 1) / pitch + 1
    let first := a + (b - a - (1 + (n - 1) * pitch)) / 2
    (List.range n.toNat).map fun (i : Nat) => ⟨key, .fill .ink 1000 (first + (i : Int) * pitch) top 1 1⟩

/-- One shape at a part's left edge `x` and the baseline `base`: a band of seven pixels above
the baseline holds the squares. -/
def shapeCalls (key : Key) (x base : Int) : Shape → List (Keyed Call)
  | .square x0 => [⟨key, .fill .ink 1000 (x + x0) (base - 7) 7 7⟩]
  | .ring x0 => [⟨key, .frame .ink (x + x0) (base - 7) 7 7 1⟩]
  | .dots x0 x1 pitch => dotCalls key (x + x0) (x + x1) (base - 4) pitch
  | .post x0 x1 reach role => [⟨key, .fill role 1000 (x + x0) (base - 7 - reach) (x1 - x0) (7 + 2 * reach)⟩]
  | .over x0 x1 => [⟨key, .fill .ink 1000 (x + x0) (base - 7) (x1 - x0) 1⟩]
  | .under x0 x1 => [⟨key, .fill .ink 1000 (x + x0) (base - 1) (x1 - x0) 1⟩]

/-- A mark at `x`: each part at its cells, from left to right. -/
def markCalls (key : Key) (x base : Int) (m : Mark) : List (Keyed Call) :=
  (m.foldl (fun (acc : Nat × List (Keyed Call)) p =>
    (acc.1 + p.cells, acc.2 ++ p.shapes.flatMap (shapeCalls key (x + 8 * acc.1) base))) (0, [])).2

/-- A mark's glyphs, for a terminal. -/
def Mark.glyphs (m : Mark) : String := String.join (m.map (·.glyph))

/-- One line of a page. -/
structure Line where
  /-- the gutter: the node's address, as `[1 0]` -/
  gutter : String
  /-- the depth of the node, for its indent -/
  depth : Nat
  /-- the node's text, in the data face -/
  text : String
  /-- the node's type, in the data face; empty when it has none -/
  type : String := ""
  /-- how the node's operation is answered, when it performs one -/
  mark : Option Mark := none
  /-- a remark after the line, in the label face -/
  note : String := ""
  /-- the node's key -/
  key : Key
  state : LineState := .plain
  /-- the line's offset from its row in logical pixels, while it moves; 0 at rest -/
  shift : Int := 0
  /-- how much of the line is written, per mille: its text cell by cell, then the rest; 1000 at
  rest -/
  reveal : Nat := 1000
deriving Repr

/-- A line at rest: no offset, and written whole. A still frame's lines are at rest. -/
def Line.AtRest (l : Line) : Prop := l.shift = 0 ∧ l.reveal = 1000

/-- A page: its title, the line under it, the heads of the two columns, its lines and its foot. -/
structure Page where
  title : String
  judgment : String := ""
  heads : String × String := ("path", "node")
  lines : Array Line := #[]
  foot : String := ""
  /-- the page's place in a sequence, as `3 / 12` -/
  place : String := ""
  /-- the width of the gutter in cells, when a sequence of pages fixes it: so the lines of every
  frame stand at one column, and only rows move between frames -/
  gutter : Option Nat := none
  /-- whether the lines' marks are drawn -/
  marks : Bool := true
  /-- a laid-out graph below the lines, and its title -/
  graph : Option (String × Laid) := none
deriving Repr

/-- The width of the gutter in cells that a page's own lines need: its widest address, and two
more. -/
def ownGutter (g : Page) : Nat :=
  let n := g.lines.foldl (fun n l => max n l.gutter.length) g.heads.1.length
  if n + 2 < 8 then 8 else n + 2

/-- The width of the gutter in cells: the sequence's, or the page's own. -/
def gutterCols (g : Page) : Int := g.gutter.getD (ownGutter g)

/-- The top of a page's graph: below its lines and a head for the graph's title. -/
def graphTop (g : Page) : Int := TOP + ROWH * g.lines.size + 8 + ROWH * 2

/-- The size of a page in logical pixels, at least `W` wide: its lines, then its graph. -/
def pageSize (W : Int) (g : Page) : Int × Int :=
  match g.graph with
  | none => (W, TOP + ROWH * g.lines.size + 8 + FOOT)
  | some (_, l) => (max W (l.width + 2 * LEFT), graphTop g + l.height + ROWH + FOOT)

/-- A page's graph as calls: its title in the label face, then the graph below. -/
def graphCalls (g : Page) : List (Keyed Call) :=
  match g.graph with
  | none => []
  | some (title, l) => textAt "" .label LEFT (graphTop g - ROWH + BASE - 8) title 400 ++
      l.calls LEFT (graphTop g)

/-- One line at its row: the band of a lit line, the gutter, then inside a cut the text, the
type and the note; a refused line is framed; last, the box that answers the pointer. -/
def lineCalls (W B : Int) (row : Nat) (l : Line) (marks : Bool := true) : List (Keyed Call) :=
  let calls := lineAt W B row l marks
  if l.shift = 0 then calls else calls.map (Keyed.move 0 l.shift)
where
  /-- The line at its row, written as far as its reveal. -/
  lineAt (W B : Int) (row : Nat) (l : Line) (marks : Bool) : List (Keyed Call) :=
  let whole := 1000 ≤ l.reveal
  let part := (l.text.take (l.text.length * l.reveal / 1000)).toString
  let l : Line := if whole then l else { l with text := part, type := "", mark := none, note := "" }
  let c0 : Int := B + INDENT * l.depth
  let y : Int := TOP + ROWH * row
  let base := y + BASE
  let cols : Int := (W - 2 * LEFT) / CELL
  let right : Int := W - LEFT
  let n := shown l.text (cols - c0)
  let end0 := c0 + n + INDENT
  let typed := !l.type.isEmpty
  let end1 := if typed then end0 + 2 + shown l.type (cols - end0 - 2) + INDENT else end0
  let mark := if marks then l.mark else none
  let end2 := if mark.isSome then end1 + MARKCOLS + 1 else end1
  let k := l.key
  (if l.state = .lit then [⟨k, .fill .rule 500 0 y W ROWH⟩] else []) ++
    cellsAt k (col 0) base l.gutter (B - 1) ++
    [⟨k, .cut (col B - 7) y W ROWH⟩] ++
    (if l.state = .refused then [⟨k, .frame .failure (col c0 - 6) (y + 2) (CELL * n + 12) (ROWH - 4) 2⟩]
      else []) ++
    cellsAt k (col c0) base l.text (cols - c0) ++
    (if typed then cellsAt k (col end0) base ":" 1 ++ cellsAt k (col (end0 + 2)) base l.type (cols - end0 - 2)
      else []) ++
    (match mark with
      | some m => markCalls k (col end1) base m
      | none => []) ++
    textAt k .label (col end2) base l.note (right - col end2) ++
    [⟨k, .uncut⟩] ++
    (if k.isEmpty then [] else [⟨k, .hit 0 y W ROWH⟩])

/-- The ground of a picture of `W` by `H` logical pixels. -/
def groundCalls (W H : Int) : List (Keyed Call) := [⟨"", .fill .ground 1000 0 0 W H⟩]

/-- The title block and the foot of a page of height `H`. Their calls carry no key. -/
def chromeCalls (W H : Int) (g : Page) : List (Keyed Call) :=
  let right := W - LEFT
  let cols := (W - 2 * LEFT) / CELL
  let B := gutterCols g
  let n : Int := g.place.length
  let none' : Key := ""
  cellsAt none' (col (cols - n)) 40 g.place n ++
    textAt none' .title LEFT 40 g.title (right - LEFT - CELL * (n + 3)) ++
    cellsAt none' LEFT 64 g.judgment cols ++
    textAt none' .label LEFT HEADS g.heads.1 (CELL * B) ++
    textAt none' .label (col B) HEADS g.heads.2 400 ++
    [⟨none', .hrule .rule LEFT HEAD_RULE (right - LEFT) 1⟩,
      ⟨none', .hrule .rule LEFT (H - FOOT) (right - LEFT) 1⟩] ++
    cellsAt none' LEFT (H - 12) g.foot cols

/-- A whole page as calls, at the width `W`: the ground, the lines, then the title block and
the foot. -/
def pageCalls (W : Int) (g : Page) : List (Keyed Call) :=
  let (W, H) := pageSize W g
  groundCalls W H ++
    (g.lines.toList.zipIdx.flatMap fun (l, i) => lineCalls W (gutterCols g) i l g.marks) ++
    graphCalls g ++ chromeCalls W H g

/-! ## The terminal: the same page as characters -/

/-- A text padded with spaces to `n` characters. -/
def padTo (n : Nat) (s : String) : String := s.pushn ' ' (n - s.length)

/-- A page as lines of characters: the title and its place, the judgment, the heads, the lines
and the foot. A lit line is marked `▸` in the gutter's first column, and a refused line `✗`. -/
def pageText (g : Page) : List String :=
  let B := (gutterCols g).toNat
  let line (l : Line) : String :=
    let mark := match l.state with
      | .plain => " "
      | .lit => "▸"
      | .refused => "✗"
    let body := "".pushn ' ' (3 * l.depth) ++ l.text ++
      (if l.type.isEmpty then "" else "  : " ++ l.type) ++
      (match l.mark with
        | some m => if g.marks then "   " ++ m.glyphs else ""
        | none => "") ++
      (if l.note.isEmpty then "" else "   " ++ l.note)
    mark ++ padTo (B - 1) l.gutter ++ body
  [g.title ++ (if g.place.isEmpty then "" else "   " ++ g.place), g.judgment,
    " " ++ padTo (B - 1) g.heads.1 ++ g.heads.2] ++
    g.lines.toList.map line ++ [g.foot]

end Tools.View
