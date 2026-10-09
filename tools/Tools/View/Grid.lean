import Tools.View.Picture

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
