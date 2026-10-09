import Tools.View.Picture

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
  /-- a remark after the line, in the label face -/
  note : String := ""
  /-- the node's key -/
  key : Key
  state : LineState := .plain
deriving Repr

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
deriving Repr

/-- The grid of `paint.h`, in logical pixels. -/
def CELL : Int := 8
def ROWH : Int := 24
def BASE : Int := 16
def LEFT : Int := 24
def TOP : Int := 104
def HEADS : Int := 88
def HEAD_RULE : Int := 96
def FOOT : Int := 32
def INDENT : Int := 3

/-- The left edge of a column of cells. -/
def col (c : Int) : Int := LEFT + CELL * c

/-- A text of data in a room of cells; nothing when it is empty or has no room. -/
def cellsAt (key : Key) (x base : Int) (s : String) (room : Int) : List (Keyed Call) :=
  if room > 0 && !s.isEmpty then [⟨key, .cells x base room.toNat s⟩] else []

/-- A text of another face in a room of pixels. -/
def textAt (key : Key) (face : Face) (x base : Int) (s : String) (room : Int) : List (Keyed Call) :=
  if s.isEmpty then [] else [⟨key, .text face x base room s⟩]

/-- The cells that a text of data takes in a room. -/
def shown (s : String) (room : Int) : Int :=
  if room ≤ 0 || s.isEmpty then 0 else min (s.length : Int) room

/-- The width of the gutter in cells that a page's own lines need: its widest address, and two
more. -/
def ownGutter (g : Page) : Nat :=
  let n := g.lines.foldl (fun n l => max n l.gutter.length) g.heads.1.length
  if n + 2 < 8 then 8 else n + 2

/-- The width of the gutter in cells: the sequence's, or the page's own. -/
def gutterCols (g : Page) : Int := g.gutter.getD (ownGutter g)

/-- The size of a page in logical pixels, at the width `W`. -/
def pageSize (W : Int) (g : Page) : Int × Int := (W, TOP + ROWH * g.lines.size + 8 + FOOT)

/-- One line at its row: the band of a lit line, the gutter, then inside a cut the text, the
type and the note; a refused line is framed; last, the box that answers the pointer. -/
def lineCalls (W B : Int) (row : Nat) (l : Line) : List (Keyed Call) :=
  let c0 : Int := B + INDENT * l.depth
  let y : Int := TOP + ROWH * row
  let base := y + BASE
  let cols : Int := (W - 2 * LEFT) / CELL
  let right : Int := W - LEFT
  let n := shown l.text (cols - c0)
  let end0 := c0 + n + INDENT
  let typed := !l.type.isEmpty
  let end1 := if typed then end0 + 2 + shown l.type (cols - end0 - 2) + INDENT else end0
  let k := l.key
  (if l.state = .lit then [⟨k, .fill .rule 500 0 y W ROWH⟩] else []) ++
    cellsAt k (col 0) base l.gutter (B - 1) ++
    [⟨k, .cut (col B - 7) y W ROWH⟩] ++
    (if l.state = .refused then [⟨k, .frame .failure (col c0 - 6) (y + 2) (CELL * n + 12) (ROWH - 4) 2⟩]
      else []) ++
    cellsAt k (col c0) base l.text (cols - c0) ++
    (if typed then cellsAt k (col end0) base ":" 1 ++ cellsAt k (col (end0 + 2)) base l.type (cols - end0 - 2)
      else []) ++
    textAt k .label (col end1) base l.note (right - col end1) ++
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
  let (_, H) := pageSize W g
  groundCalls W H ++ (g.lines.toList.zipIdx.flatMap fun (l, i) => lineCalls W (gutterCols g) i l) ++
    chromeCalls W H g

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
      (if l.note.isEmpty then "" else "   " ++ l.note)
    mark ++ padTo (B - 1) l.gutter ++ body
  [g.title ++ (if g.place.isEmpty then "" else "   " ++ g.place), g.judgment,
    " " ++ padTo (B - 1) g.heads.1 ++ g.heads.2] ++
    g.lines.toList.map line ++ [g.foot]

end Tools.View
