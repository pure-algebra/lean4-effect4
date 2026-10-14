import Tools.View.Picture
import Whatwg.Svg.Scene.Moves

/-!
# Integer scene records at the view boundary

The kit owns integer geometry. The view retains its tuple-facing picture carrier.
These conversions change records without arithmetic or rounding.
Graph connectors and peg rendering share this boundary.

Placement: `docs/research/2026-10-13-continuous-connectors-plan.md`.
The two recovery laws serve `initial-algebras-folds` and R14 under decisions row 334(3).
Their observation is integer controls, without a curve or rasterization claim.
-/

namespace Tools.View.SceneBridge
open Whatwg.Svg.Scene

def vec (p : Int × Int) : IVec := ⟨p.1, p.2⟩
def point (p : IVec) : Int × Int := (p.x, p.y)

def cubic (c : Tools.View.Cubic) : ICubic :=
  ⟨vec c.p0, vec c.p1, vec c.p2, vec c.p3⟩

def fromCubic (c : ICubic) : Tools.View.Cubic :=
  ⟨point c.p0, point c.p1, point c.p2, point c.p3⟩

def paths (cs : List ICubic × List ICubic) : List Tools.View.Cubic × List Tools.View.Cubic :=
  (cs.1.map fromCubic, cs.2.map fromCubic)

/-- The local-to-kit conversion recovers every integer control. -/
theorem from_cubic (c : Tools.View.Cubic) : fromCubic (cubic c) = c := by
  cases c
  rfl

/-- The kit-to-local conversion recovers every integer control. -/
theorem cubic_from (c : ICubic) : cubic (fromCubic c) = c := by
  cases c
  rfl

end Tools.View.SceneBridge
