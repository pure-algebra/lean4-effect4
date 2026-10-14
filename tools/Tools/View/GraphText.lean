import Tools.View.Grid

/-! Two graph rows with explicit text allocations.
The default keeps cell fitting. A chosen face changes typography within a clipped row.
The caller owns content, font metrics, and the node's allocated geometry. -/

namespace Tools.View.GraphText

/-- Row faces. `none` keeps the existing cell labels. -/
structure Style where
  first : Option Face := none
  second : Option Face := none
deriving DecidableEq, Repr

/-- One row inside its allocation. A face changes typography, never node or connector geometry. -/
def row (face : Option Face) (key : Key) (x y width : Int) (s : String) : List (Keyed Call) :=
  match face with
  | none => cellsAt key x (y + BASE) s (width / CELL)
  | some f =>
    if width ≤ 0 then [] else
      [⟨key, .cut x y width ROWH⟩] ++ textAt key f x (y + BASE) s width ++ [⟨key, .uncut⟩]

end Tools.View.GraphText
