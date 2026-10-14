import Tools.View.Tube.Skeleton
import Whatwg.Svg.Scene.PegFigure

/-! # The kit's passive peg figure at the pen boundary

The kit owns the figure data and its grid action.
`PegRender` owns the SVG boundary.
-/

namespace Tools.View.Tube

abbrev PegBody := Whatwg.Svg.Scene.PegBody
abbrev PegUnit := Whatwg.Svg.Scene.PegUnit
abbrev PegFigure := Whatwg.Svg.Scene.PegFigure
abbrev PegBody.move (d : GridPoint) (b : PegBody) : PegBody :=
  Whatwg.Svg.Scene.PegBody.move d b
abbrev PegUnit.move (d : GridPoint) (u : PegUnit) : PegUnit :=
  Whatwg.Svg.Scene.PegUnit.move d u
abbrev PegFigure.move (d : GridPoint) (f : PegFigure) : PegFigure :=
  Whatwg.Svg.Scene.PegFigure.move d f

end Tools.View.Tube
