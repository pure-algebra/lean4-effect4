import Tools.View.Tube.Belt
import Whatwg.Svg.Scene.Skeleton

/-! # The kit's grid skeleton at the pen boundary

The kit owns the syntax, contour fold, tree walk, and translation laws.
This module keeps the pen's existing names as aliases.
-/

namespace Tools.View.Tube

abbrev GridPoint := Whatwg.Svg.Scene.IVec
abbrev GridPeg := Whatwg.Svg.Scene.GridPeg
abbrev GridPeg.move (d : GridPoint) (p : GridPeg) : GridPeg :=
  Whatwg.Svg.Scene.GridPeg.move d p

abbrev GridPeg.toPeg (step : Int) (p : GridPeg) : Peg :=
  Whatwg.Svg.Scene.GridPeg.toPeg step p

abbrev Skeleton := Whatwg.Svg.Scene.Skeleton

namespace Skeleton

abbrev cap (peg : GridPeg) : Skeleton := Whatwg.Svg.Scene.Skeleton.cap peg
abbrev run (peg : GridPeg) (next : Skeleton) : Skeleton :=
  Whatwg.Svg.Scene.Skeleton.run peg next
abbrev bend (outer inner : GridPeg) (next : Skeleton) : Skeleton :=
  Whatwg.Svg.Scene.Skeleton.bend outer inner next
abbrev fork (back : GridPeg) (between after : List GridPeg) (left right : Skeleton) : Skeleton :=
  Whatwg.Svg.Scene.Skeleton.fork back between after left right
abbrev root (s : Skeleton) : GridPoint := Whatwg.Svg.Scene.Skeleton.root s
abbrev tour (s : Skeleton) : List GridPeg := Whatwg.Svg.Scene.Skeleton.tour s
abbrev walk (s : Skeleton) : List GridPoint := Whatwg.Svg.Scene.Skeleton.walk s
abbrev move (d : GridPoint) (s : Skeleton) : Skeleton := Whatwg.Svg.Scene.Skeleton.move d s
abbrev segment (a b : GridPoint) (radius : Int) : Skeleton :=
  Whatwg.Svg.Scene.Skeleton.segment a b radius
abbrev vessel (start : GridPoint) (slots : Nat) (radius : Int := 14) : Skeleton :=
  Whatwg.Svg.Scene.Skeleton.vessel start slots radius

/-- The kit law observes the contour after a grid translation. -/
theorem tour_move (d : GridPoint) (s : Skeleton) :
    (s.move d).tour = s.tour.map (GridPeg.move d) :=
  Whatwg.Svg.Scene.Skeleton.tour_move d s
/-- The kit law observes the first vertex of the tree walk. -/
theorem walk_head (s : Skeleton) : s.walk.head? = some s.root :=
  Whatwg.Svg.Scene.Skeleton.walk_head s
/-- The kit law observes the last vertex of the tree walk. -/
theorem walk_last (s : Skeleton) : s.walk.getLast? = some s.root :=
  Whatwg.Svg.Scene.Skeleton.walk_last s
/-- The kit law observes closure at the tree walk's root. -/
theorem walk_closed (s : Skeleton) : s.walk.head? = s.walk.getLast? :=
  Whatwg.Svg.Scene.Skeleton.walk_closed s

end Skeleton
end Tools.View.Tube
