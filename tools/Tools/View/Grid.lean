import Tools.View.Look

/-!
# The grid

The grid of `tools/view/paint.h` in logical pixels, and the two texts every view writes on it:
data in the monospace face, a room of cells long; another face, a room of pixels long. A cell is
8 pixels wide and a row 24 high, one base unit by three (the forms note, section 5). The page and
the graph both stand on it.
-/

namespace Tools.View

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
def MARKCOLS : Int := 6

/-! ## The title block, the foot, the gutter -/

/-- The baseline of a page's title and of its place, from the page's top. -/
def TITLE_BASE : Int := 40
/-- The baseline of the line under the title. -/
def JUDGMENT_BASE : Int := 64
/-- The foot's baseline, above the page's bottom edge. -/
def FOOT_BASE : Int := 12
/-- The room of a column head, in pixels. -/
def HEAD_ROOM : Int := 400
/-- The narrowest gutter, in cells, and the cells it keeps past its widest address. -/
def GUTTER_MIN : Nat := 8
def GUTTER_PAD : Nat := 2
/-- The space under the lines before a graph: a gap, then a row for the graph's title. -/
def GRAPH_GAP : Int := 8

/-! ## The code plane -/

/-- The cells between the widest line of a page and its code, and from the rule between them to
the code. -/
def CODE_GAP : Nat := 6
def CODE_RULE : Nat := 3
/-- The width the code plane lays the program's TypeScript out at, in cells. -/
def CODE_WIDTH : Nat := 80

/-! ## A line -/

/-- How far left of its first column a line's cut starts: the width of a refusal's frame. -/
def CUT_INSET : Int := 7
/-- The frame around a refused text: its inset left and right, its inset above and below, and
its weight, in pixels. -/
def REFUSED_SIDE : Int := 6
def REFUSED_TOP : Int := 2
def REFUSED_WEIGHT : Nat := 2

/-! ## A mark: shapes in a band of seven pixels above the baseline -/

/-- The height of a mark's band, the side of its squares. -/
def MARK_BAND : Int := 7
/-- The dots of a mark's wait stand this far above the baseline. -/
def MARK_DOTS_UP : Int := 4

/-! ## A graph -/

/-- The rows of a rank, and of a box. -/
def LEVEL : Int := 3
def BOXROWS : Int := 2
/-- The cells between two items of a rank, and from the widest rank to the first lane. -/
def GAP : Nat := 2
/-- The narrowest box, in cells, and the cells a box keeps around its longer line. -/
def BOX_MIN : Nat := 6
def BOX_PAD : Nat := 2
/-- A back edge enters its target this far above the middle of its side, so it does not meet an
edge that leaves there. -/
def BACK_RISE : Int := 4
/-- A loop's reach out of its box's side, and its half height. -/
def LOOP_REACH : Int := 2 * CELL
def LOOP_HALF : Int := 8

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

end Tools.View
