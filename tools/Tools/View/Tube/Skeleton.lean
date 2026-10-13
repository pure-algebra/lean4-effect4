import Tools.View.Tube.Belt
import Whatwg.Svg.Scene.Moves

/-!
# Grid skeletons and their contour tours

The syntax stores integer points, signed sizes, and ordered children.
The arrows are `move`, a grid action, and `tour`, a contour fold into signed pegs.
`walk` observes the rooted tree separately from the contour.
The placement note is `docs/research/2026-10-13-peg-geometry-plan.md`.
-/

namespace Tools.View.Tube

/-- An integer point on the slot grid. -/
abbrev GridPoint := Whatwg.Svg.Scene.IVec

/-- A signed radius in pixels at the twelve-pixel slot step. -/
structure GridPeg where
  point : GridPoint
  radius : Int
deriving Repr, DecidableEq, Inhabited

def GridPeg.move (d : GridPoint) (p : GridPeg) : GridPeg := ⟨p.point + d, p.radius⟩

/-- Scale both position and radius with the grid step, in thousandths of a pixel. -/
def GridPeg.toPeg (step : Int) (p : GridPeg) : Peg :=
  ⟨(p.point.x * step, p.point.y * step), p.radius * step / 12⟩

/-- A rooted contour tree. Fork decorations follow the stored clockwise child order. -/
inductive Skeleton where
  | cap (peg : GridPeg)
  | run (peg : GridPeg) (next : Skeleton)
  | bend (outer inner : GridPeg) (next : Skeleton)
  | fork (back : GridPeg) (between after : List GridPeg) (left right : Skeleton)
deriving Repr, DecidableEq, Inhabited

namespace Skeleton

/-- The first vertex of a rooted contour tree. -/
def root : Skeleton → GridPoint
  | .cap p | .run p _ | .bend p _ _ | .fork p _ _ _ _ => p.point

/-- The contour fold. A bend contributes its outer and inner peg on opposite passes. -/
def tour : Skeleton → List GridPeg
  | .cap p => [p]
  | .run p next => p :: next.tour
  | .bend outer inner next => outer :: (next.tour ++ [inner])
  | .fork back between after left right =>
    back :: (left.tour ++ between ++ right.tour ++ after)

/-- The tree walk visits each child and returns to its parent. -/
def walk : Skeleton → List GridPoint
  | .cap p => [p.point]
  | .run p next | .bend p _ next => ([p.point] ++ next.walk) ++ [p.point]
  | .fork p _ _ left right =>
    ((([p.point] ++ left.walk) ++ [p.point]) ++ right.walk) ++ [p.point]

/-- Move every vertex and every local contour decoration by one grid vector. -/
def move (d : GridPoint) : Skeleton → Skeleton
  | .cap p => .cap (p.move d)
  | .run p next => .run (p.move d) (next.move d)
  | .bend outer inner next => .bend (outer.move d) (inner.move d) (next.move d)
  | .fork back between after left right =>
    .fork (back.move d) (between.map (GridPeg.move d)) (after.map (GridPeg.move d))
      (left.move d) (right.move d)

/-- Contour translation commutes with the contour fold. -/
theorem tour_move (d : GridPoint) (s : Skeleton) :
    (s.move d).tour = s.tour.map (GridPeg.move d) := by
  induction s with
  | cap p => rfl
  | run p next ih => simp only [move, tour, List.map_cons, ih]
  | bend outer inner next ih =>
    simp only [move, tour, List.map_cons, List.map_append, List.map_nil, ih]
  | fork back between after left right ihl ihr =>
    simp only [move, tour, List.map_cons, List.map_append, ihl, ihr]

/-- The tree walk starts at its root. -/
theorem walk_head (s : Skeleton) : s.walk.head? = some s.root := by
  cases s <;> rfl

/-- The tree walk ends at its root. -/
theorem walk_last (s : Skeleton) : s.walk.getLast? = some s.root := by
  cases s <;> simp only [walk, root, List.getLast?_concat, List.getLast?_singleton]

/-- The walk is closed on the observation of its first and last vertex. -/
theorem walk_closed (s : Skeleton) : s.walk.head? = s.walk.getLast? :=
  (walk_head s).trans (walk_last s).symm

/-- A straight run between two cap pegs. -/
def segment (a b : GridPoint) (radius : Int) : Skeleton :=
  .run ⟨a, radius⟩ (.cap ⟨b, radius⟩)

/-- A vessel surrounds its first and last slot centres. Capacity changes its length. -/
def vessel (start : GridPoint) (slots : Nat) (radius : Int := 14) : Skeleton :=
  segment start ⟨start.x + (max slots 1 - 1 : Nat), start.y⟩ radius

end Skeleton
end Tools.View.Tube
