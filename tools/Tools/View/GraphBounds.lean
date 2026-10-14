import Tools.View.Graph
import Tools.View.PaintBounds

/-!
Graph viewport fitting from allocated rectangles and resolved drawing calls.
The caller resolves a look before supplying the calls.
The returned shift moves the calls without changing routing geometry.
Text metrics remain unmeasured.
Placement: `docs/research/2026-10-13-graph-bounds-plan.md`.
-/

namespace Tools.View.GraphBounds
open Whatwg.Svg.Scene

/-- A fitted viewport, its drawing translation and the text-metric observation. -/
structure Viewport where
  bounds : IBox
  shift : Int × Int
  size : Int × Int
  unmeasuredText : Bool
deriving DecidableEq, Repr

/-- Fit already-resolved calls together with the laid graph's allocated canvas. -/
def viewport (laid : Laid) (calls : List (Keyed Call)) (halo : Nat := 0) : Viewport :=
  let report := PaintBounds.calls calls
  let bounds := PaintBounds.fit (IBox.ofSize 0 (max 0 laid.width) (max 0 laid.height)) report halo
  { bounds, shift := (-bounds.x0, -bounds.y0), size := (bounds.width, bounds.height),
    unmeasuredText := report.unmeasuredText }

/-- Move resolved calls into their fitted viewport, retaining their keys and call order. -/
def Viewport.calls (v : Viewport) (calls : List (Keyed Call)) : List (Keyed Call) :=
  calls.map (Keyed.move v.shift.1 v.shift.2)

end Tools.View.GraphBounds
